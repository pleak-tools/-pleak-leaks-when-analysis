open GrbGraphs;;
open GrbCommons;;

let removeDead dg =
	let checkNodes = Queue.create ()
	and liveNodes = Hashtbl.create (DG.foldnodes (fun _ i -> i+1) dg 0)
	in
	DG.foldnodes (fun n () -> if n.nkind.inadvview then (Hashtbl.add liveNodes n.id (); Queue.add n checkNodes) else ()) dg ();
	while not (Queue.is_empty checkNodes) do
		let n = Queue.take checkNodes
		in
		DG.nodefoldedges (fun ((ct,_),_,_) () ->
			let csrc = connectionsources ct
			in
			IdtSet.iter (fun cs ->
				if Hashtbl.mem liveNodes cs then () else
				begin
					Hashtbl.add liveNodes cs ();
					Queue.add (DG.findnode cs dg) checkNodes
				end
			) csrc
		) n ()
	done;
	let changedg = ref dg
	in
	DG.foldnodes (fun n () ->
		if Hashtbl.mem liveNodes n.id then () else
			(changedg := DG.remnode n.id !changedg)
	) dg ();
	!changedg
;;

let foldIdentity dg =
  let newdg = DG.foldedges (fun ((conn,eid),tgt,prt) dgcurr ->
  	let srcidset = connectionsources conn
  	in
  	let changes = ref false
  	in
  	let newconn = IdtSet.fold (fun srcid currconn ->
  		let n = DG.findnode srcid dgcurr
  		in
  		match n.nkind.nodeintlbl with
  			| NNId -> changes := true; DG.nodefoldedges (fun ((upconn,_),_,_) conn' ->
  				composeIxM conn' n.id upconn
  				) n currconn
  			| _ -> currconn
  	) srcidset conn
  	in
	if !changes then DG.addedge ((newconn,eid), tgt.id, prt) (DG.remedge eid dgcurr)
	else dgcurr
  ) dg dg
  in
  newdg
;;

let splitIndexTypes dg =
	let nodeTbl = Hashtbl.create (DG.foldnodes (fun _ i -> i+1) dg 0)
	in
	DG.foldnodes (fun n () ->
		let (AITT a) = n.inputindextype
		and (IxM m) = n.ixtypemap
		in
		let newInputIndices = Array.mapi (fun x _ -> if x = 0 then n.id else NewName.get ()) a
		in
		let newindices = Array.mapi (fun idx -> function None -> raise (Failure "splitIndexTypes") | Some ((), x, _) -> (newInputIndices.(idx),newInputIndices.(x)) ) m
		in
		Hashtbl.add nodeTbl n.id (Array.map fst newindices, Array.map snd newindices)
	) dg ();
	let dg' = DG.foldnodes (fun n dgcurr ->
		let (AITT a) = n.inputindextype
		and (AITT b) = n.outputindextype
		and (IxM m) = n.ixtypemap
		in
		let (inpIndices,_outIndices) = Hashtbl.find nodeTbl n.id
		in
		let changedg = ref dgcurr
		in
		Array.iteri (fun idx nnid ->
			let outpidx,newindexmap = match m.(idx) with
				| None -> raise (Failure "splitIndexTypes2")
				| Some ((), c, backmap) -> c, Some ((), 0, backmap)
			in
			let nn = {
				nkind = n.nkind;
				id = nnid;
				inputindextype = AITT [| a.(idx) |];
				outputindextype = AITT [| b.(outpidx) |];
				inputs = PortMap.empty;
				ixtypemap = IxM [| newindexmap |];
			}
			in changedg := DG.addnode nn !changedg
		) inpIndices;
		!changedg
	) dg DG.empty
	in
	let dg'' = DG.foldedges (fun ((IxM m,eid),tgtn,prt) dgcurr ->
		let (headIndices,_) = Hashtbl.find nodeTbl tgtn.id
		in
		let changedg = ref dgcurr
		in
		Array.iteri (fun idx melem ->
			match melem with
				| None -> raise (Failure "splitIndexTypes3")
				| Some (srcid, c, backmap) ->
					let (_,tailIndices) = Hashtbl.find nodeTbl srcid
					in
					changedg := DG.addedge ((IxM [| Some (tailIndices.(c), 0, backmap) |], NewName.get ()), headIndices.(idx), prt) !changedg
		) m;
		!changedg
	) dg dg'
	in
	dg''
;;

let areIndicesInOrderForANode n =
	let (AITT a) = n.inputindextype
	and (AITT b) = n.outputindextype
	and (IxM m) = n.ixtypemap
	in
	if Array.length a <> Array.length m then raise (Failure ("Indices not in order: node " ^ (NewName.to_string n.id) ^ " has mismatching lengths of a and m" )) else
	Array.iteri (fun idx aelem ->
		let melem = m.(idx)
		in
		match melem with
			| None -> raise (Failure ("Indices not in order: node " ^ (NewName.to_string n.id) ^ " has None inside m") )
			| Some ((), c, melemarr) ->
			begin
				if c >= Array.length b then raise (Failure ("Indices not in order: node " ^ (NewName.to_string n.id) ^ " requires more elements in b than it has") ) else
				let belem = b.(idx)
				in
				if Array.length belem <> Array.length melemarr then raise (Failure ("Indices not in order: node " ^ (NewName.to_string n.id) ^ " has wrong number of point-backs") ) else
				Array.iteri (fun idx ptr ->
					let it1 = belem.(idx)
					in
					if ptr >= Array.length aelem then raise (Failure ("Indices not in order: node " ^ (NewName.to_string n.id) ^ " has too few dimensions") ) else
					let it2 = aelem.(ptr)
					in
					if it1 <> it2 then raise (Failure ("Indices not in order: node " ^ (NewName.to_string n.id) ^ " has inequal dimensions") ) else ()
				) melemarr
			end
	) a
;;

let areIndicesInOrderForAEdge dg ((IxM cc, eid), tgt, _) =
	let (AITT tgta) = tgt.inputindextype
	in
	if Array.length tgta <> Array.length cc then raise (Failure ("Indices not in order: edge " ^ (NewName.to_string eid) ^ " into node " ^ (NewName.to_string tgt.id) ^ " has wrong number of handled components" )) else
	Array.iteri (fun idx ccelem ->
		let aelem = tgta.(idx)
		in
		match ccelem with
			| None -> ()
			| Some (srcid, compnum, backmap) ->
				if not (DG.hasnode srcid dg) then raise (Failure ("Indices not in order: edge " ^ (NewName.to_string eid) ^ " into node " ^ (NewName.to_string tgt.id) ^ " is missing a source" )) else
				let src = DG.findnode srcid dg
				in
				let (AITT srcb) = src.outputindextype
				in
				if compnum >= Array.length srcb then raise (Failure ("Indices not in order: edge " ^ (NewName.to_string eid) ^ " into node " ^ (NewName.to_string tgt.id) ^ " points to a too large component" )) else
				if Array.length srcb.(compnum) <> Array.length backmap then raise (Failure ("Indices not in order: edge " ^ (NewName.to_string eid) ^ " into node " ^ (NewName.to_string tgt.id) ^ " has the wrong number of elements in backmap" )) else
				Array.iteri (fun bidx ptr ->
					let barrelem = srcb.(compnum).(bidx)
					in
					if ptr >= Array.length tgta.(idx) then raise (Failure ("Indices not in order: edge " ^ (NewName.to_string eid) ^ " into node " ^ (NewName.to_string tgt.id) ^ " has backmap pointing too far" )) else
					let aarrelem = tgta.(idx).(ptr)
					in
					if barrelem <> aarrelem then raise (Failure ("Indices not in order: edge " ^ (NewName.to_string eid) ^ " into node " ^ (NewName.to_string tgt.id) ^ " has backmap connecting different dimensions" )) else ()
				) backmap
	) cc
;;

let areIndicesInOrder s dg =
	print_string ("Entering areIndicesInOrder: " ^ s ^ "\n");
	DG.foldnodes (fun n () ->
		areIndicesInOrderForANode n
	) dg ();
	DG.foldedges (fun edgetuple () -> areIndicesInOrderForAEdge dg edgetuple) dg ();
	dg
;;

let foldThingsTogether dg suitableIntLbl =
	let rec makeLongEdge (IxM m) =
		let Some (midid, comp, prt) = m.(0)
		in
		let midn = DG.findnode midid dg
		in
		if suitableIntLbl midn.nkind.nodeintlbl then
			DG.nodefoldedges (fun ((cc, _),_,_) ll ->
				let lx = makeLongEdge cc
				in
				(List.map (fun (IxM m') -> composeIxM (IxM m) midid (IxM m')) lx) @ ll
			) midn []
		else [IxM m]
	in
	DG.foldnodes (fun n dgcurr ->
		if suitableIntLbl n.nkind.nodeintlbl then
			DG.nodefoldedges (fun ((cc,eid),tgt,prt) dgnext ->
				let lx = makeLongEdge cc
				in
				List.fold_right (fun cc' dg' -> DG.addedge ((cc', NewName.get ()), tgt.id, prt) dg') lx (DG.remedge eid dgnext)
			) n dgcurr
		else dgcurr
	) dg dg
;;

let foldAndsTogether dg = foldThingsTogether dg (function NNAnd -> true | _ -> false);;

let foldMaxsTogether dg = foldThingsTogether dg (function NNMaximum _ -> true | _ -> false);;

let reduceNodeDim dg nid =
	let oldToNewMapping useddims =
		(*print_string ("Call oldToNewMapping with [|" ^ (String.concat "; " (List.map string_of_bool (Array.to_list useddims))) ^ "|]\n") ; *)
		let len = Array.length useddims
		in
		if len = 0 then begin (* print_string "Return from oldToNewMapping\n"; *) ([||], [||], 0) end else
		begin
		let oldToNewInpDims = Array.make len 0
		in
		for i = 1 to (len - 1) do
			if useddims.(i-1) then
				oldToNewInpDims.(i) <- oldToNewInpDims.(i-1) + 1
			else
				oldToNewInpDims.(i) <- oldToNewInpDims.(i-1)
		done;
		let numnewinpdims = if useddims.(len-1) then oldToNewInpDims.(len - 1) + 1 else oldToNewInpDims.(len-1)
		in
		let newToOldInpDims = Array.make numnewinpdims 0
		in
		for i = 0 to (len - 1) do
			if useddims.(i) then newToOldInpDims.(oldToNewInpDims.(i)) <- i
		done;
		(*print_string "Return from oldToNewMapping\n"; *)
		(oldToNewInpDims, newToOldInpDims, numnewinpdims)
		end
	and pushDimsTogether a newToOldDims =
		(*print_string "Call pushDimsTogether\n";*)
		let res = Array.init (Array.length newToOldDims) (fun i -> a.(newToOldDims.(i)))
		in
		(*print_string "Return from pushDimsTogether\n";*)
		res
	in	
	let n = DG.findnode nid dg
	in
	let (AITT a) = n.inputindextype
	and (AITT b) = n.outputindextype
	and (IxM m) = n.ixtypemap
	in
	let Some ((), _, mCont) = m.(0)
	in
	let useddims = Array.make (Array.length a.(0)) false
	in
	(match n.nkind.nodeintlbl with
		| NNTakeDim s -> Array.iteri (fun idx (_,tp) -> if tp = Some s then useddims.(idx) <- true) a.(0)
		| NNInput _ | NNInputExists _ | NNDimEq ->
			Array.iteri (fun i _ -> useddims.(i) <- let (vt,_) = a.(0).(i) in vt <> VUnit) a.(0)
		| _ -> ()
	);
	(*print_string "Point 1\n";*)
	DG.nodefoldedges (fun ((IxM m,_eid),_tgt,_prt) () ->
		let Some (_,_,backmap) = m.(0)
		in
		Array.iter (fun idx -> useddims.(idx) <- true) backmap
	) n ();
	(*print_string "Point 2\n";*)
	let outuseddims = Array.map (fun i -> useddims.(i)) mCont
	in
	(*print_string "Point 3\n";*)
	let (oldToNewInpDims, newToOldInpDims, numnewinpdims) = oldToNewMapping useddims
	and (oldToNewOutpDims, newToOldOutpDims, numnewoutpdims) = oldToNewMapping outuseddims
	in
	let mContNew = Array.init numnewoutpdims (fun i -> oldToNewInpDims.(mCont.(newToOldOutpDims.(i))))
	in
	(*print_string "Point 4\n";*)
	let nn = {
		nkind = n.nkind;
		id = n.id;
		inputindextype = AITT [| pushDimsTogether a.(0) newToOldInpDims |];
		outputindextype = AITT [| pushDimsTogether b.(0) newToOldOutpDims |];
		inputs = PortMap.empty;
		ixtypemap = IxM [| Some ((), 0, mContNew) |];
	}
	in
	areIndicesInOrderForANode nn;
	let dg' = DG.addnode nn (DG.remnode n.id dg)
	in
	let dg2 = DG.nodefoldedges (fun ((IxM em, eid), tgt, prt) dgcurr ->
		let Some (srcid, cpl, emCont) = em.(0)
		in
		let emContNew = Array.map (fun i -> oldToNewInpDims.(i)) emCont
		in
		DG.addedge ((IxM [|Some (srcid, cpl, emContNew) |], eid), tgt.id, prt) dgcurr
	) n dg'
	in
	DG.nodefoldoutedges dg (fun ((IxM em, eid), tgt, prt) dgcurr ->
		let Some (srcid, cpl, emCont) = em.(0)
		in
		let emContNew = pushDimsTogether emCont newToOldOutpDims
		in
		DG.addedge ((IxM [| Some (srcid, cpl, emContNew) |], eid), tgt.id, prt) dgcurr
	) n dg2
;;

module GraphForTopolSort =
struct
	type t = DG.t
	
	module V =
	struct
		type t = NewName.idtype
		
		let compare = Pervasives.compare
		let hash = Hashtbl.hash
		let equal id1 id2 = (id1 = id2)
	end
	
	let iter_vertex f dg = DG.foldnodes (fun n () -> f n.id) dg ()
	
	let iter_succ f dg nid = ignore (DG.nodefoldoutedges dg (fun (_,tgt,_) s -> if IdtSet.mem tgt.id s then s else (f tgt.id; IdtSet.add tgt.id s)) (DG.findnode nid dg) IdtSet.empty); ()
	
end;;

module TopolSorter = Graph.Topological.Make(GraphForTopolSort);;
module SCCFinder = Graph.Components.Make(GraphForTopolSort);;

let reduceAllNodeDim dg =
	TopolSorter.fold (fun nid dgnew -> reduceNodeDim dgnew nid) dg dg;;

let putTogetherSameNodes dg n1 n2 =
	if n1.nkind.nodeintlbl <> n2.nkind.nodeintlbl then None else
	let (AITT a1) = n1.inputindextype
	and (AITT a2) = n2.inputindextype
	and (AITT b1) = n1.outputindextype
	and (AITT b2) = n2.outputindextype
	in
	let haveSameDims a1e a2e =
		let a1s = Array.copy a1e
		and a2s = Array.copy a2e
		in
		Array.sort Pervasives.compare a1s;
		Array.sort Pervasives.compare a2s;
		a1s = a2s
	in
	if not ((haveSameDims a1.(0) a2.(0)) && (haveSameDims b1.(0) b2.(0))) then None else
	let inEdgesOfNode n =
		DG.nodefoldedges (fun ((IxM cc,eid),_,prt) currmap ->
			let Some (srcid,_,_) = cc.(0)
			in
			let srcmap = try PortMap.find prt currmap with Not_found -> IdtMap.empty
			in
			let srcset = try IdtMap.find srcid srcmap with Not_found -> IdtSet.empty
			in
			PortMap.add prt (IdtMap.add srcid (IdtSet.add eid srcset) srcmap) currmap
		) n PortMap.empty
	in
	let rec matchDimensions edges1 edges2 foundMap =
		if PortMap.is_empty edges1 then
		begin
			if not (PortMap.is_empty edges2) then None else
			let freeDims1 =
				let res = ref IntSet.empty
				in
				Array.iteri (fun idx v -> if v = None then res := IntSet.add idx !res) foundMap;
				!res
			and freeDims2 =
				let res = ref (IntSet.from_list (intfromto 0 ((Array.length foundMap) - 1)))
				in
				Array.iter (fun v -> match v with Some x -> (res := IntSet.remove x !res) | None -> ()) foundMap;
				!res
			in
			if not (IntSet.is_empty freeDims1) then
			begin
				let fd1 = IntSet.choose freeDims1
				in
				IntSet.fold (fun fd2 alreadyfound ->
					match alreadyfound with
						| Some _ -> alreadyfound
						| None ->
							if a1.(0).(fd1) = a2.(0).(fd2) then
							begin
								let currFoundMap = Array.copy foundMap
								in
								currFoundMap.(fd1) <- Some fd2;
								matchDimensions edges1 edges2 currFoundMap
							end
							else None
				) freeDims2 None
			end else
			let a3map = Array.make (Array.length a1.(0)) IntSet.empty
			and bMap = Array.make (Array.length b1.(0)) 0
			and Some ((),_,backmap1) = let (IxM m) = n1.ixtypemap in m.(0)
			and Some ((),_,backmap2) = let (IxM m) = n2.ixtypemap in m.(0)
			in
			let realMap = try 
				Array.map (fun (Some x) -> x) foundMap
				with Match_failure exarg -> begin
					print_string "matchDimensions: ";
					print_string (NewName.to_string n1.id);
					print_string " and ";
					print_string (NewName.to_string n2.id);
					print_newline ();
					raise (Match_failure exarg)
				end
			in
			Array.iteri (fun idx bm ->
				a3map.(realMap.(bm)) <- IntSet.add idx a3map.(realMap.(bm))
			) backmap1;
			try
				Array.iteri (fun idx bm ->
					let someidx = IntSet.choose a3map.(bm)
					in
					bMap.(idx) <- someidx;
					a3map.(bm) <- IntSet.remove someidx a3map.(bm)
				) backmap2;
				if Array.fold_right (fun s b -> b && (IntSet.is_empty s)) a3map true then Some bMap else None
			with Not_found -> None
		end else
		let (prt, srcmap1) = PortMap.min_binding edges1
		in
		if not (PortMap.mem prt edges2) then None else
		let srcmap2 = PortMap.find prt edges2
		in
		let (srcid, eset1) = IdtMap.min_binding srcmap1
		in
		if not (IdtMap.mem srcid srcmap2) then None else
		let eset2 = IdtMap.find srcid srcmap2
		in
		let eid1 = IdtSet.choose eset1
		in
		let eset1inner = IdtSet.remove eid1 eset1
		and ((IxM cc1,_),_,_) = DG.findedge eid1 dg
		in
		let srcmap1inner = if IdtSet.is_empty eset1inner then IdtMap.remove srcid srcmap1 else IdtMap.add srcid eset1inner srcmap1
		and Some (_,_,ebmap1) = cc1.(0)
		in
		let edges1inner = if IdtMap.is_empty srcmap1inner then PortMap.remove prt edges1 else PortMap.add prt srcmap1inner edges1
		in
		IdtSet.fold (fun eid2 alreadyFound ->
			match alreadyFound with
				| Some _ -> alreadyFound
				| None ->
					let currFoundMap = Array.copy foundMap
					in
					let ((IxM cc2,_),_,_) = DG.findedge eid2 dg
					in
					let Some (_,_,ebmap2) = cc2.(0)
					in
					let incompatible = ref false
					in
					Array.iteri (fun idx dim1 ->
						let dim2 = ebmap2.(idx)
						in
						match currFoundMap.(dim1) with
							| None -> currFoundMap.(dim1) <- Some dim2
							| Some dim2' -> if dim2 = dim2' then () else incompatible := true
					) ebmap1;
					if !incompatible then None else
					let eset2inner = IdtSet.remove eid2 eset2
					in
					let srcmap2inner = if IdtSet.is_empty eset2inner then IdtMap.remove srcid srcmap2 else IdtMap.add srcid eset2inner srcmap2
					in
					let edges2inner = if IdtMap.is_empty srcmap2inner then PortMap.remove prt edges2 else PortMap.add prt srcmap2inner edges2
					in
					matchDimensions edges1inner edges2inner currFoundMap
		) eset2 None
	in
	let perhapsMap = match n1.nkind.nodeintlbl with
		| NNTakeDim _ -> Some [|0|]
		| _ -> matchDimensions (inEdgesOfNode n1) (inEdgesOfNode n2) (Array.make (Array.length a1.(0)) None)
	in
	match perhapsMap with
		| None -> None
		| Some dimsMap -> 
			Some (DG.nodefoldoutedges dg (fun ((IxM cc,eid),tgtn,prt) dgcurr ->
				let Some (_,_,backmap) = cc.(0)
				in
				let newbackmap = Array.map (fun idx -> backmap.(idx)) dimsMap
				in
				DG.addedge ((IxM [|Some (n1.id, 0, newbackmap) |], eid), tgtn.id, prt) dgcurr
			) n2 (DG.remnode n2.id dg))
;;

let putTogetherNodes dg =
	let tsnodesL = TopolSorter.fold (fun nid l -> nid :: l) dg []
	and removedNodes = ref IdtSet.empty
	and changedg = ref dg
	in
	let tsnodes = Array.of_list tsnodesL
	in
	for i = (Array.length tsnodes) - 1 downto 1 do
		if IdtSet.mem tsnodes.(i) !removedNodes then () else
		for j = i-1 downto 0 do
			if IdtSet.mem tsnodes.(j) !removedNodes then () else
			let n1 = DG.findnode tsnodes.(i) !changedg
			and n2 = DG.findnode tsnodes.(j) !changedg
			in
			match putTogetherSameNodes !changedg n1 n2 with
				| None -> ()
				| Some dgnew -> begin
					changedg := dgnew;
					removedNodes := IdtSet.add tsnodes.(j) !removedNodes
				end
		done
	done;
	!changedg
;;

let simplifyCoalesce dg n =
	if n.nkind.nodeintlbl <> NNOperation OPCoalesce then None else
	let inps = DG.nodefoldedges (fun (((IxM cc,eid),_,PortOperInput sq) as edgerecord) imcurr ->
		let Some (srcid,_,_) = cc.(0)
		in
		let srcn = DG.findnode srcid dg
		in
		match srcn.nkind.nodeintlbl with
			| NNOperation (OPNull _) ->
				IntMap.add sq (edgerecord, false) imcurr
			| _ -> IntMap.add sq (edgerecord, true) imcurr
	) n IntMap.empty
	in
	let nonNull = IntMap.exists (fun _ (_,v) -> v) inps
	in
	let nnew = { n with
		nkind = if nonNull then nkId n.nkind.outputtype else nkOperation 0 n.nkind.outputtype (OPNull n.nkind.outputtype);
		inputs = PortMap.empty
	}
	in
	let found = ref false
	in
	let dg' = IntMap.fold (fun idx ((conn,_,_), isGood) dgcurr ->
		if isGood && (not !found) then
		begin
			found := true;
			DG.addedge (conn, n.id, (PortSingle n.nkind.outputtype)) dgcurr
		end
		else dgcurr
	) inps (DG.changenode nnew dg)
	in
	Some dg'
;;

let simplifyICA suitableIntLbl hasZeroIntLbl possnkZero hasUnitIntLbl nkUnit dg n =
	if not (suitableIntLbl n.nkind.nodeintlbl) then None else
	let nvtype = n.nkind.outputtype
	in
	let hasFalseInput =
		let foundyet = ref false
		in
		DG.nodefoldedges (fun ((IxM cc,eid),_,_) () ->
			if !foundyet then () else
			let Some (srcid, _, _) = cc.(0)
			in
			let srcn = DG.findnode srcid dg
			in
			foundyet := hasZeroIntLbl srcn.nkind.nodeintlbl
		) n ();
		!foundyet
	in
	if hasFalseInput then
	begin
		let Some nkZero = possnkZero
		in
		let nnew = {n with
			inputs = PortMap.empty;
			nkind = nkZero nvtype;
		}
		in
		Some (DG.changenode nnew dg)
	end else
	begin
		let foundTrue = ref false
		in
		let simpTrueDg = DG.nodefoldedges (fun ((IxM cc,eid),_,_) dgcurr ->
			let Some (srcid, _, _) = cc.(0)
			in
			let srcn = DG.findnode srcid dg
			in
			if hasUnitIntLbl srcn.nkind.nodeintlbl then
				(foundTrue := true; DG.remedge eid dgcurr)
			else
				dgcurr
		) n dg
		in
		let inpcount = DG.nodefoldedges (fun _ i -> i+1) (DG.findnode n.id simpTrueDg) 0
		in
		let afterCountDg =
			if inpcount = 0 then
				let nnew = {n with
					inputs = PortMap.empty;
					nkind = nkUnit nvtype;
				}
				in
				(foundTrue := true; DG.changenode nnew simpTrueDg)
			else if inpcount = 1 then
				let nnew = {n with
					inputs = PortMap.empty;
					nkind = nkId nvtype
				}
				in
				(foundTrue:= true;
				DG.nodefoldedges (fun ((cc,eid),_,_) dgcurr -> DG.addedge ((cc,eid), n.id, PortSingle nvtype) dgcurr) (DG.findnode n.id simpTrueDg) (DG.changenode nnew simpTrueDg))
			else simpTrueDg
		in
		if !foundTrue then Some afterCountDg else None
	end
;;

let simplifyAnd = simplifyICA
	(function NNAnd -> true | _ -> false)
	(function NNFalse -> true | _ -> false)
	(Some (fun _ -> nkFalse))
	(function NNTrue -> true | _ -> false)
	(fun _ -> nkTrue)
;;

let simplifyOr = simplifyICA
	(function NNOr -> true | _ -> false)
	(function NNTrue -> true | _ -> false)
	(Some (fun _ -> nkTrue))
	(function NNFalse -> true | _ -> false)
	(fun _ -> nkFalse)
;;

let simplifyAddition = simplifyICA
	(function NNSum -> true | _ -> false)
	(fun _ -> false)
	None
	(function NNOperation (OPIntConst 0) -> true | NNOperation (OPRealConst 0.0) -> true | _ -> false)
	(function VInteger -> nkOperation 0 VInteger (OPIntConst 0) | VReal -> nkOperation 0 VReal (OPRealConst 0.0))
;;

let simplifyMax = simplifyICA
	(function NNMaximum -> true | _ -> false)
	(fun _ -> false)
	None
	(function NNOperation (OPIntConst 0) -> true | NNOperation (OPRealConst 0.0) -> true | _ -> false)
	(function VInteger -> nkOperation 0 VInteger (OPIntConst 0) | VReal -> nkOperation 0 VReal (OPRealConst 0.0))
;;

let additionToSum dg n =
	if n.nkind.nodeintlbl <> NNOperation OPPlus then None else
	let nnew = {n with
		nkind = nkSum VInteger;
		inputs = PortMap.empty;
	}
	in
	let dgwid = DG.changenode nnew dg
	in
	let dgnew = DG.nodefoldedges (fun ((cc,eid),_,prt) dgcurr ->
		DG.addedge ((cc, eid), n.id, PortMulti VInteger) dgcurr
	) n dgwid
	in
	Some dgnew
	

let simplifyMerge dg n =
	if (match n.nkind.nodeintlbl with NNMerge _ -> false | _ -> true) then None else
	let NNMerge vtype = n.nkind.nodeintlbl
	in
	if (PortSet.cardinal n.nkind.ports) <> 1 then None else
	let nnew = {n with
		nkind = nkId vtype;
		inputs = PortMap.empty;
	}
	in
	let dgwid = DG.changenode nnew dg
	in
	let dgnew = DG.nodefoldedges (fun ((cc,eid),_,prt) dgcurr ->
		DG.addedge ((cc, eid), n.id, PortSingle vtype) dgcurr
	) n dgwid
	in
	Some dgnew
;;

let dontOutputNulls dg n =
	if (match n.nkind.nodeintlbl with NNOutput _ -> false | _ -> true) then None else
	let NNOutput inputDescription = n.nkind.nodeintlbl
	in
	let srcidpl = ref None
	and cntrlpl = ref None
	and srcidbackmappl = ref None
	and cntrlbackmappl = ref None
	and vtpl = ref None
	in
	DG.nodefoldedges (fun ((IxM cc,eid),_,prt) () ->
		match prt with
			| PortSingle vt ->
				let Some (srcid,_,backmap) = cc.(0)
				in (srcidpl := Some srcid; srcidbackmappl := Some backmap; vtpl := Some vt)
			| PortSingleB ->
				let Some (srcid,_,backmap) = cc.(0)
				in (cntrlpl := Some srcid; cntrlbackmappl := Some backmap)
	) n ();
	let Some srcid = !srcidpl
	in
	let src = DG.findnode srcid dg
	in
	match src.nkind.nodeintlbl with
		| NNOperation (OPNull _)
		| NNOperation (OPIntConst _)
		| NNOperation (OPStringConst _)
		| NNOperation (OPRealConst _)
		| NNOperation (OPBoolConst _) -> Some (DG.remnode n.id dg)
		| NNITE _ ->
		begin
			let Some cntrlid = !cntrlpl
			and Some srcbackmap = !srcidbackmappl
			and Some cntrlbackmap = !cntrlbackmappl
			and Some vt = !vtpl
			and (AITT na) = n.inputindextype
			in
			let condidpl = ref None
			and condbackmappl = ref None
			and trueidpl = ref None
			and truebackmappl = ref None
			and falseidpl = ref None
			and falsebackmappl = ref None
			in
			DG.nodefoldedges (fun ((IxM cc, _), _, prt) () ->
				match prt with
					| PortSingleB ->
						let Some (srcid,_,backmap) = cc.(0)
						in (condidpl := Some srcid; condbackmappl := Some backmap)
					| PortTrue _ ->
						let Some (srcid,_,backmap) = cc.(0)
						in (trueidpl := Some srcid; truebackmappl := Some backmap)
					| PortFalse _ ->
						let Some (srcid,_,backmap) = cc.(0)
						in (falseidpl := Some srcid; falsebackmappl := Some backmap)
			) src ();
			let Some condid = !condidpl
			and Some condbackmap = !condbackmappl
			and Some trueid = !trueidpl
			and Some truebackmap = !truebackmappl
			and Some falseid = !falseidpl
			and Some falsebackmap = !falsebackmappl
			in
			let falsenode = DG.findnode falseid dg
			and truenode = DG.findnode trueid dg
			and condnode = DG.findnode condid dg
			in
			let notnode = {
				nkind = nkNot;
				id = NewName.get ();
				inputindextype = condnode.outputindextype;
				outputindextype = condnode.outputindextype;
				inputs = PortMap.empty;
				ixtypemap = identityIndexMap () condnode.outputindextype;
			}
			in
			let trueconj = {
				nkind = nkAnd;
				id = NewName.get ();
				inputindextype = n.inputindextype;
				outputindextype = n.inputindextype;
				inputs = PortMap.empty;
				ixtypemap = identityIndexMap () n.inputindextype;
			}
			in
			let falseconj = { trueconj with id = NewName.get (); }
			and trueoutput = { trueconj with id = NewName.get (); nkind = nkOutput vt inputDescription; }
			and falseoutput = { trueconj with id = NewName.get (); nkind = nkOutput vt inputDescription; }
			in
			let IxM srccc = src.ixtypemap
			and AITT srca = src.inputindextype
			and AITT srcb = src.outputindextype
			in
			let Some ((), _, srcixm) = srccc.(0)
			in
			let srcixminv = Array.make (Array.length srca.(0)) 0
			in
			Array.iteri (fun idx ptr ->
				srcixminv.(ptr) <- idx
			) srcixm;
			Some (
			DG.addedge ((IxM [| Some (notnode.id, 0, Array.init (Array.length condbackmap) (fun i -> srcbackmap.(srcixminv.(condbackmap.(i)))) ) |], NewName.get ()), falseconj.id, PortStrictB) (
			DG.addedge ((IxM [| Some(cntrlid, 0, cntrlbackmap) |], NewName.get ()), falseconj.id, PortStrictB) (
			DG.addedge ((IxM [| Some (condid, 0, Array.init (Array.length condbackmap) (fun i -> srcbackmap.(srcixminv.(condbackmap.(i)))) ) |], NewName.get ()), trueconj.id, PortStrictB) (
			DG.addedge ((IxM [| Some(cntrlid, 0, cntrlbackmap) |], NewName.get ()), trueconj.id, PortStrictB) (
			DG.addedge ((identityIndexMap condid condnode.outputindextype, NewName.get ()), notnode.id, PortSingleB) (
			DG.addedge ((IxM [| Some (trueconj.id, 0, Array.init (Array.length na.(0)) (fun x -> x)) |], NewName.get ()), trueoutput.id, PortSingleB) (
			DG.addedge ((IxM [| Some (truenode.id, 0, Array.init (Array.length truebackmap) (fun i -> srcbackmap.(srcixminv.(truebackmap.(i))))) |], NewName.get ()), trueoutput.id, PortSingle vt) (
			DG.addedge ((IxM [| Some (falseconj.id, 0, Array.init (Array.length na.(0)) (fun x -> x)) |], NewName.get ()), falseoutput.id, PortSingleB) (
			DG.addedge ((IxM [| Some (falsenode.id, 0, Array.init (Array.length falsebackmap) (fun i -> srcbackmap.(srcixminv.(falsebackmap.(i))))) |], NewName.get ()), falseoutput.id, PortSingle vt) (
			DG.addnode trueoutput (
			DG.addnode falseoutput (
			DG.addnode trueconj (
			DG.addnode falseconj (
			DG.addnode notnode (
			DG.remnode n.id dg
			)))))))))))))))
		end
		| _ -> None
;;

let longorOfFalse dg n =
	if (match n.nkind.nodeintlbl with NNLongOr -> false | _ -> true) then None else
	let hasFalseInput = DG.nodefoldedges (fun ((IxM cc,_),_,_) b ->
		if b then true else
		let Some (srcid,_,_) = cc.(0)
		in
		let srcn = DG.findnode srcid dg
		in
		srcn.nkind.nodeintlbl = NNFalse
	) n false
	in
	if not hasFalseInput then None else
	let nn = { n with
		nkind = nkFalse;
		inputs = PortMap.empty;
	}
	in
	Some (DG.changenode nn dg)
;;

let simplifyArithmetic dg =
	let funchain = [simplifyCoalesce; simplifyAnd; simplifyOr; longorOfFalse; additionToSum; simplifyAddition; simplifyMax; simplifyMerge; dontOutputNulls]
	in
	TopolSorter.fold (fun nid dgnew ->
		List.fold_left (fun dgcurr simpfun ->
			let n = DG.findnode nid dgcurr
			in
			match simpfun dgcurr n with
			| None -> dgcurr
			|Some dg' -> dg'
		) dgnew funchain
	) dg dg;;

let iseqToDimEqNode dg n =
	if n.nkind.nodeintlbl <> NNIsEq then dg else
	let edgesAsList = DG.nodefoldedges (fun ((IxM cc,eid),_,_) l ->
		let Some (srcid,_,backmap) = cc.(0)
		in
		let srcn = DG.findnode srcid dg
		in
		(srcn,backmap,eid) :: l
	) n []
	in
	if edgesAsList = [] then dg else
	if List.tl edgesAsList = [] then DG.changenode {n with inputs = PortMap.empty; nkind = nkTrue} dg else
	let (src1,bm1,eid1) = List.hd edgesAsList
	and (src2,bm2,eid2) = List.hd (List.tl edgesAsList)
	in
	if src1.id <> src2.id then dg else
	if (match src1.nkind.nodeintlbl with NNTakeDim _ -> false | _ -> true) then dg else
	let (AITT a) = src1.inputindextype
	in
	let nnew = {n with
		nkind = nkAnd;
		inputs = PortMap.empty
	}
	in
	let usedA = Array.mapi (fun idx v -> (idx,v)) a.(0)
	in
	let newInps = Array.fold_right (fun (idx,dimname) ll ->
		let dimeqid = NewName.get ()
		and indextype = AITT [| [| dimname; dimname |] |]
		in
		let dimeqn = {
			nkind = nkDimEq;
			id = dimeqid;
			inputindextype = indextype;
			outputindextype = indextype;
			inputs = PortMap.empty;
			ixtypemap = IxM [|Some ((), 0, [|0;1|]) |];
		}
		in
		let backmap = [| bm1.(idx); bm2.(idx) |]
		in
		(dimeqn, backmap) :: ll
	) usedA []
	in
	List.fold_right (fun (dimeqn, backmap) dgcurr ->
		let dg1 = DG.addnode dimeqn dgcurr
		in
		DG.addedge ((IxM [| Some (dimeqn.id, 0, backmap) |], NewName.get ()),n.id, PortStrictB) dg1
	) newInps (DG.changenode nnew dg)
;;

let iseqAddDimEqNode dg n =
	if n.nkind.nodeintlbl <> NNIsEq then dg else
	let srcbackmappl = ref None
	and srcnodepl = ref None
	in
	let hasUniqueInput = DG.nodefoldedges (fun ((IxM cc, _),_,_) bb ->
		if bb then true else
		let Some (srcid, _, backmap) = cc.(0)
		in
		let srcn = DG.findnode srcid dg
		in
		match srcn.nkind.nodeintlbl with
			| NNInput (_, _, true) -> begin
				srcbackmappl := Some backmap;
				srcnodepl := Some srcn;
				true
				end
			| _ -> false
	) n false
	in
	if not hasUniqueInput then dg else
	let Some srcn = !srcnodepl
	and Some srcbackmap = !srcbackmappl
	and intBackMap =
		let (IxM nm) = n.ixtypemap
		in
		let Some ((), _, fwdmap) = nm.(0)
		in
		let res = Array.make (Array.length fwdmap) 0
		in
		for i = 0 to (Array.length fwdmap) - 1 do
			res.(fwdmap.(i)) <- i
		done;
		res
	in
	let changedg = ref dg
	in begin
		DG.nodefoldoutedges dg (fun ((IxM cc1, eid1), nOutId1, _) () ->
			let nOut = DG.findnode nOutId1.id !changedg
			in
			if nOut.nkind.nodeintlbl <> NNAnd then () else
			let (AITT nOutA) = nOut.inputindextype
			in
			DG.nodefoldoutedges dg (fun ((IxM cc2, eid2), nOutId2, _) () ->
				if (nOutId1.id = nOutId2.id) && ((NewName.to_string eid1) < (NewName.to_string eid2)) then
				begin
					let Some (_, _, obackmap1) = cc1.(0)
					and Some (_, _, obackmap2) = cc2.(0)
					in
					let eqsListPre = Array.fold_right (fun ptr ll ->
						let atnOut = intBackMap.(ptr)
						in
						let d1 = obackmap1.(atnOut)
						and d2 = obackmap2.(atnOut)
						in
						if d1 = d2 then ll else
						let (d1',d2') = if d1 < d2 then (d1,d2) else (d2,d1)
						in
						(d1',d2') :: ll
					) srcbackmap []
					in
					let eqsList = List.sort_uniq Pervasives.compare eqsListPre
					in
					List.iter (fun (d1, d2) ->
						let eqdimnodedims = AITT [| [| nOutA.(0).(d1); nOutA.(0).(d2) |] |]
						in
						let eqdimnode = {
							nkind = nkDimEq;
							id = NewName.get ();
							inputs = PortMap.empty;
							inputindextype = eqdimnodedims;
							outputindextype = eqdimnodedims;
							ixtypemap = identityIndexMap () eqdimnodedims;
						}
						in
						changedg :=
							DG.addedge ((IxM [| Some (eqdimnode.id, 0, [| d1; d2 |]) |], NewName.get ()), nOut.id, PortStrictB)
							(DG.addnode eqdimnode !changedg)
					) eqsList
				end
			) n ()
		) n ();
		!changedg
	end
;;
	

let iseqToDimEq dg = 
	DG.foldnodes (fun nold dgcurr -> 
		let dginterm = iseqToDimEqNode dgcurr (DG.findnode nold.id dgcurr)
		in
		iseqAddDimEqNode dginterm (DG.findnode nold.id dginterm)
	) dg dg;;

module ClassRepr = (
struct
	type t = int array;;
	
	let make n = Array.init n (fun x -> x);;
	
	let rec getClass r d =
		if r.(d) = d then d else
		let dc = getClass r r.(d)
		in
		r.(d) <- dc;
		dc;;
	
	let joinClasses r d1 d2 =
		let dc1 = getClass r d1
		and dc2 = getClass r d2
		in
		let (dd1,dd2) = (min dc1 dc2, max dc1 dc2)
		in
		r.(dd2) <- dd1;;
	
	let length r = Array.length r;;
	
	let applyTypeMap r ixm =
		let newlength = Array.length ixm
		in
		let nr = make newlength
		in
		for i = 0 to (newlength - 2) do
			for j = (i+1) to (newlength - 1) do
				let cli = getClass r ixm.(i)
				and clj = getClass r ixm.(j)
				in
				if cli = clj then joinClasses nr i j
			done;
		done;
		nr;;
end : sig
	type t
	val make : int -> t
	val getClass : t -> int -> int
	val joinClasses : t -> int -> int -> unit
	val length : t -> int
	val applyTypeMap : t -> int array -> t
end);;

let collectReducedDims dg n =
	let AITT a = n.inputindextype
	in
	let clmaparr = ClassRepr.make (Array.length a.(0))
	in
	let eqDimListPr = DG.nodefoldedges (fun ((IxM cc, eid), _, _) ll ->
		let Some (srcid, _, backmap) = cc.(0)
		in
		let srcn = DG.findnode srcid dg
		in
		if srcn.nkind.nodeintlbl <> NNDimEq then ll else
		let d1pr = backmap.(0)
		and d2pr = backmap.(1)
		in
		let (d1,d2) = (min d1pr d2pr, max d1pr d2pr)
		in
		(d1,d2) :: ll
	) n []
	in
	List.iter (fun (v1,v2) -> ClassRepr.joinClasses clmaparr v1 v2) eqDimListPr;
	let eqDimList = List.filter (fun (x,y) -> x <> y) (List.map (fun i -> (ClassRepr.getClass clmaparr i, i)) (intfromto 0 ((ClassRepr.length clmaparr) - 1))) (* eqDimList is the list of pairs of to-be-joined dimensions at the input of the AND-node *)
	in eqDimList
;;


let reduceOneAndDimension dg n =
	if n.nkind.nodeintlbl <> NNAnd then None else
	let (outpNodeIds, onlyOutputSuccs, inputDescription) = DG.nodefoldoutedges dg (fun ((_,_), tgtn, prt) (currIds, currFlag, currIDesc) ->
		if not currFlag then (IdtSet.empty, false, RLSet.empty) else
		match tgtn.nkind.nodeintlbl, prt with
			| NNOutput iDesc, PortSingleB -> (IdtSet.add tgtn.id currIds, true, RLSet.union iDesc currIDesc)
			| _,_ -> (IdtSet.empty, false, RLSet.empty)
	) n (IdtSet.empty, true, RLSet.empty)
	in
	if not onlyOutputSuccs then None else
	let AITT a = n.inputindextype
	and eqDimList = collectReducedDims dg n
	in
	if eqDimList = [] then None else
	begin
		let reducDimsNum = List.length eqDimList
		and lostDims = IntSet.of_list (List.map snd eqDimList)
		in
		let survivingDimsNum = (Array.length a.(0)) - reducDimsNum
		in
		let equalDimsIxmap = Array.make survivingDimsNum 0
		and outpixt = Array.make survivingDimsNum (NoValue, None)
		in
		let ii = ref 0
		in
		for i = 0 to ((Array.length equalDimsIxmap) - 1) do
			while IntSet.mem !ii lostDims do
				ii := !ii + 1
			done;
			equalDimsIxmap.(i) <- !ii;
			outpixt.(i) <- a.(0).(!ii);
			ii := !ii + 1
		done;
		let genericDimReducer = {
			nkind = nkEqualDims VBoolean eqDimList;
			id = n.id;
			inputs = PortMap.empty;
			inputindextype = n.inputindextype;
			outputindextype = AITT [| outpixt |];
			ixtypemap = IxM [| Some ((), 0, equalDimsIxmap) |];
		}
		and newAndNode = {
			nkind = nkAnd;
			id = NewName.get ();
			inputs = PortMap.empty;
			inputindextype = AITT [| outpixt |];
			outputindextype = AITT [| outpixt |];
			ixtypemap = IxM [| Some ((), 0, Array.init survivingDimsNum (fun x -> x)) |];
		}
		and oldAndNode = {n with
			nkind = nkId VBoolean;
			inputs = PortMap.empty;
		}
		in
		let reduceOutputNode dg0 nOut =
			let controlEdgePl = ref None
			and dataEdgePl = ref None
			and dataEdgeTypePl = ref None
			in
			DG.nodefoldedges (fun ((IxM cc,_),_, prt) () ->
				match prt with
					| PortSingleB -> controlEdgePl := cc.(0)
					| PortSingle vt -> (dataEdgePl := cc.(0); dataEdgeTypePl := Some vt)
			) nOut ();
			let Some (_, _, oldEdgeBM) = !controlEdgePl
			and Some (srcid, _, dataEdgeBM) = !dataEdgePl
			and Some dataVt = !dataEdgeTypePl
			in
			let (AITT aOut) = nOut.inputindextype
			in
			let liveDims = Array.make (Array.length aOut.(0)) false
			in
			Array.iter (fun oldIdx ->
				liveDims.(oldEdgeBM.(oldIdx)) <- true
			) equalDimsIxmap;
			let oldToNewDims = Array.make (Array.length aOut.(0)) 0
			in
			let currNewDim = ref 0
			in
			for i = 0 to ((Array.length oldToNewDims) - 1) do
				if liveDims.(i) then
				begin
					oldToNewDims.(i) <- !currNewDim;
					currNewDim := !currNewDim + 1
				end
			done;
			let newToOldDims = Array.make !currNewDim 0
			in
			for i = 0 to ((Array.length oldToNewDims) - 1) do
				if liveDims.(i) then
				begin
					newToOldDims.(oldToNewDims.(i)) <- i
				end
			done;
			let outpNodeEqDimList = List.map (fun (x,y) -> (oldEdgeBM.(x), oldEdgeBM.(y))) eqDimList
			and thisOutpIxt = Array.init (Array.length newToOldDims) (fun i -> aOut.(0).(newToOldDims.(i)))
			in
			let dataDimReducer = {
				nkind = nkEqualDims dataVt outpNodeEqDimList;
				id = nOut.id;
				inputindextype = nOut.inputindextype;
				outputindextype = AITT [| thisOutpIxt  |];
				inputs = PortMap.empty;
				ixtypemap = IxM [| Some ((), 0, newToOldDims) |];
			}
			and newOutpNode = {
				nkind = nkOutput dataVt inputDescription;
				id = NewName.get ();
				inputindextype = AITT [| thisOutpIxt |];
				outputindextype = AITT [| thisOutpIxt |];
				inputs = PortMap.empty;
				ixtypemap = IxM [| Some ((), 0, Array.init (Array.length thisOutpIxt) (fun x -> x)) |];
			}
			in
(*			DG.addedge ((IxM [| Some (srcid, 0, Array.init (Array.length dataEdgeBM) (fun x -> oldToNewDims.(dataEdgeBM.(x)))) |], NewName.get ()), dataDimReducer.id, PortSingle dataVt) (  *)
			DG.addedge ((IxM [| Some (srcid, 0, dataEdgeBM) |], NewName.get ()), dataDimReducer.id, PortSingle dataVt) (
			DG.addedge ((IxM [| Some (newAndNode.id, 0, Array.init (Array.length outpixt) (fun x -> oldToNewDims.(oldEdgeBM.(equalDimsIxmap.(x))))) |], NewName.get()), newOutpNode.id, PortSingleB) (
			DG.addedge ((IxM [| Some (dataDimReducer.id, 0, Array.init (Array.length thisOutpIxt) (fun x -> x)) |], NewName.get ()), newOutpNode.id, PortSingle dataVt) (
			DG.addnode newOutpNode (
			DG.addnode dataDimReducer dg0))))
		in
		(*let dg1 = DG.addedge ((IxM [| Some (newAndNode.id, 0, equalDimsIxmap) |], NewName.get ()), n.id, PortSingle VBoolean) (DG.addnode newAndNode (DG.changenode oldAndNode dg)) *)
		let dg1 = DG.addnode newAndNode dg
		in
		let dg2 = DG.nodefoldedges (fun ((cc, eid), _, _) dgcurr ->
			let dimreducn = {genericDimReducer with id = NewName.get ();}
			in
			DG.addedge ((cc, NewName.get ()), dimreducn.id, PortSingle VBoolean)
				(DG.addedge ((IxM [| Some (dimreducn.id, 0,  Array.init survivingDimsNum (fun x -> x))  |], NewName.get ()), newAndNode.id, PortStrictB)
				(DG.addnode dimreducn dgcurr))
		) n dg1
		in
		let dg3 = IdtSet.fold (fun onodeid dgcurr ->
			let nOut = DG.findnode onodeid dgcurr
			in
			reduceOutputNode dgcurr nOut
		) outpNodeIds dg2
		in
		Some dg3
	end
;;

(* TO BE ADDED BEGIN

let reduceOneAndDimension dg n =
	if n.nkind.nodeintlbl <> NNAnd then None else
	if not onlyOutputSuccs then None else
	let AITT a = n.inputindextype
	and eqDimList = collectReducedDims dg n
	in
	if eqDimList = [] then None else
	begin
		let changedg = ref dg
		in
		let pushTogetherDims origLen eqDimsList =
			let usedDims =
				let res = Array.make origLen true
				in
				List.iter (fun (_,d) -> res.(d) <- false) eqDimsList;
				res
			in
			let eqMap = 
				let res = Array.init origLen (fun x -> x)
				in
				List.iter (fun (d1,d2) -> res.(d2) <- d1) eqDimsList;
				res
			in
			let newLen = origLen - (List.length eqDimsList)
			in
			let oldToNew = Array.make (-1) origLen
			and newToOld = Array.make 0 newLen
			in
			if origLen > 0 then
			begin
				let currPtr = ref 0
				in
				for i = 0 to (Array.length usedDims) - 1 do
					if usedDims.(i) then
					begin
						oldToNew.(i) <- !currPtr;
						currPtr := !currPtr + 1
					end else
						oldToNew.(i) <- oldToNew.(eqMap.(i))
				done;
				for i = 0 to (Array.length usedDims) - 1 do
					if usedDims.(i) then
						newToOld.(oldToNew.(i)) <- i
				done
			end;
			(newLen, oldToNew, newToOld)
		let pushTogetherMap srcOldLen srcNewLen tgtOldLen tgtNewLen srcOldToNew srcNewToOld tgtOldToNew tgtNewToOld oldMap =
			Array.init srcNewLen (fun x -> tgtOldToNew.(oldMap.(srcNewToOld.(x))))
		in
		let pushEqDimsAlongAMap eqDimsList naLen nbLen pushMap =
			let eqMap = 
				let res = Array.init naLen (fun x -> x)
				in
				List.iter (fun (d1,d2) -> res.(d2) <- d1) eqDimsList;
				res
			in
			let downEqList =
				let res = ClassRepr.init nbLen
				in
				for d1 = 0 to (Array.length na0) - 1 do
					for d2 = d1 + 1 to (Array.length na0) - 1 do
						let dd1 = eqMap.(d1)
						and dd2 = eqMap.(d2)
						in
						if dd1 = dd2 then
						begin
							let s1 = pushMap.(d1)
							and s2 = pushMap.(d2)
							in 
							if (s1 <> -1) && (s2 <> -1) then
								ClassRepr.joinClasses res s1 s2
						end
					done;
				done;
				let llres = ref []
				in
				for i = 0 to (ClassRepr.length res) - 1 do
					let j = ClassRepr.getClass i
					in
					if i <> j then llres := (j,i) :: !llres
				done;
				!llres
			in
			downEqList
		in
		let pushEqDimsListDownNode n eqDimsList =
			let (AITT a) = n.inputindextype
			and (AITT b) = n.outputindextype
			and (IxM mm) = n.ixtypemap
			in
			let na0 = a.(0)
			and nb0 = b.(0)
			and Some ((), _, fwdmap) = mm.(0)
			in
			let invFwdMap =
				let res = Array.make (Array.length na0) (-1)
				in
				Array.iteri (fun idx ptr -> res.(ptr) <- idx) fwdmap;
				res
			in
			pushEqDimsAlongAMap eqDimsList (Array.length na0) (Array.length nb0) invFwdMap
		in
		let pushEqDimsListDownEdge eqDimsList srcb0 tgta0 backmap =
			pushEqDimsAlongAMap eqDimsList (Array.length srcb0) (Array.length tgta0) backmap
		in
		let rec updateNode nid eqDimsList addedEqDimsNodes incomingConnection =
			let n = DG.findnode nid !changedg
			in
			let downEqDimsList = pushEqDimsListDownNode n eqDimsList
			in
			


	end
;;

WILL CONTINUE WHEN THE DELIVERABLE HAS BEEN WRITTEN

TO BE ADDED END *)

let reduceAndDimension dg = DG.foldnodes (fun nold dgcurr -> match reduceOneAndDimension dgcurr (DG.findnode nold.id dgcurr) with None -> dgcurr | Some dg' -> dg') dg dg;;

let reduceOneLongorDimension dg n =
	if n.nkind.nodeintlbl <> NNLongOr then None else
	let (andid, albackmap, aledgeid) =
		let srcidpl = ref None
		and albackmappl = ref None
		and aledgeidpl = ref None
		in
		DG.nodefoldedges (fun ((IxM cc, eid),_,prt) () ->
			if prt = PortSingleB then
			begin
				let Some (srcid',_,albackmap') = cc.(0)
				in
				srcidpl := Some srcid';
				albackmappl := Some albackmap';
				aledgeidpl := Some eid
			end
		) n ();
		let Some res1 = !srcidpl
		and Some res2 = !albackmappl
		and Some res3 = !aledgeidpl
		in
		(res1, res2, res3)
	in
	let andnode = DG.findnode andid dg
	in
	if andnode.nkind.nodeintlbl <> NNAnd then None else
	let AITT a = andnode.inputindextype
	and AITT b = andnode.outputindextype
	and AITT la = n.inputindextype
	and AITT lb = n.outputindextype
	and IxM mm = andnode.ixtypemap
	and IxM lm = n.ixtypemap
	in
	let Some ((), _, laintmap) = lm.(0)
	and Some ((), _, aaintmap) = mm.(0)
	in
	let contracteddims =
		let lolivedims = Array.make (Array.length la.(0)) false
		in
		Array.iter (fun x -> lolivedims.(x) <- true) laintmap;
		Array.map not lolivedims
	and aaintmapinv =
		let zzz = Array.make (Array.length aaintmap) 0
		in
		for i = 0 to (Array.length aaintmap) - 1 do
			zzz.(aaintmap.(i)) <- i
		done;
		zzz
	in
	let clmaparr = ClassRepr.make (Array.length a.(0))
	in
	let eqDimListPr = DG.nodefoldedges (fun ((IxM cc, eid), _, _) ll ->
		let Some (srcid, _, backmap) = cc.(0)
		in
		let srcn = DG.findnode srcid dg
		in
		if srcn.nkind.nodeintlbl <> NNDimEq then ll else
		let d1pr = albackmap.(aaintmapinv.(backmap.(0)))
		and d2pr = albackmap.(aaintmapinv.(backmap.(1)))
		in
		if contracteddims.(d1pr) || contracteddims.(d2pr) then
			let (d1,d2) = (min d1pr d2pr, max d1pr d2pr)
			in
			(d1,d2) :: ll
		else ll
	) andnode []
	in
	if eqDimListPr = [] then None else
	begin
	List.iter (fun (v1,v2) -> ClassRepr.joinClasses clmaparr v1 v2) eqDimListPr;
	let eqDimList = List.filter (fun (x,y) -> x <> y) (List.map (fun i -> (ClassRepr.getClass clmaparr i, i)) (intfromto 0 ((ClassRepr.length clmaparr) - 1)))
	in
	let reducDimsNum = List.length eqDimList
	and lostDims = IntSet.of_list (List.map snd eqDimList)
	in
	let survivingDimsNum = (Array.length a.(0)) - reducDimsNum
	in
	let equalDimsIxmap = Array.make survivingDimsNum 0
	and outpixt = Array.make survivingDimsNum (NoValue, None)
	in
	let ii = ref 0
	in
	for i = 0 to ((Array.length equalDimsIxmap) - 1) do
		while IntSet.mem !ii lostDims do
			ii := !ii + 1
		done;
		equalDimsIxmap.(i) <- !ii;
		outpixt.(i) <- a.(0).(!ii);
		ii := !ii + 1
	done;
	let genericDimReducer = {
		nkind = nkEqualDims VBoolean eqDimList;
		id = NewName.get ();
		inputs = PortMap.empty;
		inputindextype = n.inputindextype;
		outputindextype = AITT [| outpixt |];
		ixtypemap = IxM [| Some ((), 0, equalDimsIxmap) |];
	}
	in
	Some (
	DG.addedge ((IxM [| Some (andid, 0, albackmap) |], NewName.get ()), genericDimReducer.id, PortSingle VBoolean) (
	DG.addedge ((IxM [| Some (genericDimReducer.id, 0, equalDimsIxmap) |], NewName.get ()), n.id, PortSingleB) (
	DG.addnode genericDimReducer (
	DG.remedge aledgeid dg))))
	end
;;

let reduceLongorDimension dg = DG.foldnodes (fun nold dgcurr -> match reduceOneLongorDimension dgcurr (DG.findnode nold.id dgcurr) with None -> dgcurr | Some dg' -> dg') dg dg;;

let moveOverEqualDims dg n =
	match n.nkind.nodeintlbl with
	| NNEqualDims dimpairlist ->
	begin
		let (AITT na) = n.inputindextype
		and (AITT nb) = n.outputindextype
		and (IxM nm) = n.ixtypemap
		in
		let Some ((),_,ntmap) = nm.(0)
		in
		let nclmaparr = Array.init (Array.length na.(0)) (fun x -> x)
		in
		List.iter (fun (d1,d2) -> nclmaparr.(d2) <- d1) dimpairlist;
		let ntmapinv =
			let res = Array.make (Array.length na.(0)) 0
			in
			Array.iteri (fun idx bmidx -> res.(bmidx) <- idx) ntmap;
			List.iter (fun (d1,d2) -> res.(d2) <- res.(d1)) dimpairlist;
			res
		in
		let Some (srcid, backmap, eid) = DG.nodefoldedges (fun ((IxM cc,eid),_,_) _ ->
			let Some (srcid, _, backmap) = cc.(0)
			in
			Some (srcid,backmap,eid)
		) n None
		in
		let srcn = DG.findnode srcid dg
		in
		let (AITT sa) = srcn.inputindextype
		and (AITT sb) = srcn.outputindextype
		and (IxM sm) = srcn.ixtypemap
		in
		let Some ((), _, stmap) = sm.(0)
		in
		if (match srcn.nkind.nodeintlbl with NNEqualDims _ -> true | _ -> false) then None
		else if (match srcn.nkind.nodeintlbl with NNDimEq -> true | _ -> false) && (nclmaparr.(backmap.(0)) = nclmaparr.(backmap.(1))) then
		(
			let nnew = {n with
				nkind = nkTrue;
				inputs = PortMap.empty;
				inputindextype = n.outputindextype;
				ixtypemap = IxM [| Some ((), 0, Array.init (Array.length nb.(0)) (fun x -> x)) |];
			}
			in
			Some (DG.changenode nnew dg)
		)
		else ( if (Array.length sb.(0)) = 0 then
		(
			let nnew = {n with
				nkind = nkId n.nkind.outputtype;
				inputs = PortMap.empty;
				inputindextype = n.outputindextype;
				ixtypemap = IxM [| Some ((), 0, Array.init (Array.length nb.(0)) (fun x -> x)) |];
			}
			in
			Some (DG.addedge ((IxM [| Some (srcid, 0, [||] ) |] ,NewName.get ()), n.id, PortSingle n.nkind.outputtype) (DG.changenode nnew dg))
		)
		else
		(
			let sbkeys = Array.init (Array.length sb.(0)) (fun x -> (nclmaparr.(backmap.(x)), x))
			in
			Array.sort Pervasives.compare sbkeys;
			let (nidx0, sidx0) = sbkeys.(0)
			in
			let currnidx = ref nidx0
			and currsidx = ref sidx0
			in
			sbkeys.(0) <- (sidx0, sidx0);
			for i = 1 to ((Array.length sbkeys) - 1) do
				let (nidxi,sidxi) = sbkeys.(i)
				in
				if nidxi = !currnidx then
				begin
					sbkeys.(i) <- (sidxi, !currsidx)
				end
				else
				begin
					sbkeys.(i) <- (sidxi, sidxi);
					currnidx := nidxi;
					currsidx := sidxi
				end
			done;
			Array.sort Pervasives.compare sbkeys; (* Now sbkeys.(i) is equal to (i, class of i) *)
			let sbOnlyKeys = Array.map snd sbkeys
			and (sbOldToNew, newsblen) =
				let c = ref 0
				in
				let res = Array.make (Array.length sbkeys) 0
				in
				for i = 1 to ((Array.length sbkeys) - 1) do
					let (idx,cidx) = sbkeys.(i) (* idx = i *)
					in
					if idx = cidx then
					begin
						c := !c + 1;
						res.(i) <- !c
					end
				done;
				(res, !c + 1)
			in
			let sbNewToOld =
				let res = Array.make newsblen 0
				in
				for i = 1 to ((Array.length sbkeys) - 1) do
					let (idx,cidx) = sbkeys.(i) (* idx = i *)
					in
					if idx = cidx then
					begin
						res.(sbOldToNew.(i)) <- i
					end
				done;
				res
			in
			let sbNew = Array.init newsblen (fun x -> sb.(0).(sbNewToOld.(x)))
			in
			let contractOutps = Array.fold_right (fun (idx,cidx) l -> if idx <> cidx then (cidx,idx) :: l else l) sbkeys []
			in
			let nnew = {n with
				nkind = nkId n.nkind.outputtype;
				inputs = PortMap.empty;
				inputindextype = n.outputindextype;
				ixtypemap = IxM [| Some ((), 0, Array.init (Array.length nb.(0)) (fun x -> x)) |];
			}
			in
			let opToIdBackmap = Array.init newsblen (fun x -> ntmapinv.(backmap.(sbNewToOld.(x))))
			in
			let contractInpsClass = ClassRepr.make (Array.length sa.(0))
			in
			List.iter (fun (idx,cidx) -> ClassRepr.joinClasses contractInpsClass stmap.(idx) stmap.(cidx)) contractOutps;
			let contractInps = Array.fold_right (fun (x,y) l -> if x <> y then (x,y) :: l else l) (Array.init (ClassRepr.length contractInpsClass) (fun i -> (ClassRepr.getClass contractInpsClass i ,i))) []
			in
			let (saOldToNew, newsalen) =
				let c = ref 0
				in
				let res = Array.make (Array.length sa.(0)) 0
				in
				for idx = 1 to ((Array.length sa.(0)) - 1) do
					let cidx = ClassRepr.getClass contractInpsClass idx
					in
					if idx = cidx then
					begin
						c := !c + 1;
						res.(idx) <- !c
					end
				done;
				(res, !c + 1)
			in
			let saNewToOld =
				let res = Array.make newsalen 0
				in
				for idx = 1 to ((Array.length sa.(0)) - 1) do
					let cidx = ClassRepr.getClass contractInpsClass idx
					in
					if idx = cidx then
					begin
						res.(saOldToNew.(idx)) <- idx
					end
				done;
				res
			in
			let saNew = Array.init newsalen (fun x -> sa.(0).(saNewToOld.(x)))
			in
			let sNewIxMap = Array.init newsblen (fun i -> saOldToNew.(stmap.(sbNewToOld.(i))))
			in
			let newOpNode = {
				nkind = srcn.nkind;
				id = NewName.get ();
				inputs = PortMap.empty;
				inputindextype = AITT [| saNew |];
				outputindextype = AITT [| sbNew |];
				ixtypemap = IxM [| Some ((), 0, sNewIxMap) |];
			}
			and genericDimReducer = {
				nkind = nkEqualDims (n.nkind.outputtype) contractInps;
				id = n.id;
				inputs = PortMap.empty;
				inputindextype = srcn.inputindextype;
				outputindextype = AITT [| saNew |];
				ixtypemap = IxM [| Some ((), 0, saNewToOld) |];
			}
			in 
			let dg1 = DG.addedge ((IxM [| Some (newOpNode.id, 0, opToIdBackmap) |],NewName.get ()), n.id, PortSingle (n.nkind.outputtype)) (DG.addnode newOpNode (DG.changenode nnew dg))
			and needsReduc = contractInps <> []
			in
			let dg2 = DG.nodefoldedges (fun ((cc, eid), _, prt) dgcurr ->
				let dimreducn = {genericDimReducer with id = NewName.get (); nkind = nkEqualDims ((portdesc prt).inputkind) contractInps}
				in
				if needsReduc then
					DG.addedge ((cc, NewName.get ()), dimreducn.id, PortSingle (portdesc prt).inputkind)
						(DG.addedge ((IxM [| Some (dimreducn.id, 0,  Array.init (Array.length saNew) (fun x -> x))  |], NewName.get ()), newOpNode.id, prt)
						(DG.addnode dimreducn dgcurr))
				else
					DG.addedge ((cc, NewName.get ()), newOpNode.id, prt) dgcurr
			) srcn dg1
			in
			Some dg2
		) )
	end
	| _ -> None
;;

let moveAllOverEqualDims dg =
	let currdg = ref dg
	and hasChanges = ref true
	and iterNum = ref 1
	and printGraphs = true
	in
	while !hasChanges do
		let dgNow = !currdg
		in
		hasChanges := false;
		currdg := TopolSorter.fold (fun nid dgnew ->
			try
				let n = DG.findnode nid dgnew
				in
				let res = moveOverEqualDims dgnew n
				in
				match res with
					| None -> dgnew
					| Some dg' -> (hasChanges := true; dg')
			with Not_found -> (print_string "Could not find node no. "; print_string (NewName.to_string nid); print_newline (); dgnew)
		) dgNow dgNow;
		currdg := removeDead !currdg;
		if printGraphs then
		begin
			let oc = open_out ("moveOver_" ^ (string_of_int !iterNum) ^ ".dot")
			in
			GrbPrint.printgraph oc !currdg;
			close_out oc;
			iterNum := !iterNum + 1
		end
	done;
	!currdg
;;

module IdtInstSet = MySet (
struct
	type t = NewName.idtype * int array
	let compare = Pervasives.compare
end
);;

let findPotentiallyEqualDims dg n =
	let (AITT a) = n.inputindextype
	and (IxM m) = n.ixtypemap
	in
	let Some ((), _, backmap) = m.(0)
	in
	let dimclass = ClassRepr.make (Array.length a.(0))
	in
	if (match n.nkind.nodeintlbl with NNAnd -> false | _ -> true) then dimclass else
	let fwdmap = Array.make (Array.length a.(0)) 0
	in
	for i = 0 to (Array.length a.(0)) - 1 do
		fwdmap.(backmap.(i)) <- i
	done;
	let idarr = Array.init (Array.length a.(0)) (fun x -> x)
	in
	for i = 0 to (Array.length a.(0)) - 2 do
		for j = i + 1 to (Array.length a.(0)) - 1 do
			if (a.(0).(i) = a.(0).(j)) && (i = ClassRepr.getClass dimclass i) && (j = ClassRepr.getClass dimclass j) then
			begin
				let ijeqarr = Array.copy idarr
				in
				ijeqarr.(j) <- i;
				let (diffdimns, samedimns) = DG.nodefoldedges (fun ((IxM cc, _), _, _) (currdiffns, currsamens) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let samebackmap = Array.map (fun x -> if x = j then i else x) backmap
					in
					(IdtInstSet.add (srcid, backmap) currdiffns, IdtInstSet.add (srcid, samebackmap) currsamens)
				) n (IdtInstSet.empty, IdtInstSet.empty)
				in
				if IdtInstSet.subset samedimns diffdimns then ClassRepr.joinClasses dimclass fwdmap.(i) fwdmap.(j)
			end
		done;
	done;
	dimclass;;

let removeOneOutputControlDims dg n allDimclass =
	if (match n.nkind.nodeintlbl with NNOutput _ -> false | _ -> true) then dg else
	let controlEdgePl = ref None
	and controlEdgeIdPl = ref None
	and dataEdgePl = ref None
	and dataEdgeTypePl = ref None
	and dataEdgeIdPl = ref None
	in
	DG.nodefoldedges (fun ((IxM cc, eid),_, prt) () ->
		match prt with
			| PortSingleB -> (controlEdgePl := cc.(0); controlEdgeIdPl := Some eid)
			| PortSingle vt -> (dataEdgePl := cc.(0); dataEdgeTypePl := Some vt; dataEdgeIdPl := Some eid)
	) n ();
	let Some (andnodeid, _, oldEdgeBM) = !controlEdgePl
	and Some (srcid, _, dataEdgeBM) = !dataEdgePl
	and Some dataVt = !dataEdgeTypePl
	and Some controlEdgeId = !controlEdgeIdPl
	and Some dataEdgeId = !dataEdgeIdPl
	in
	let andnode = DG.findnode andnodeid dg
	in
	let (IxM andnodecc) = andnode.ixtypemap
	in
	let Some ((),_,andnodefwdmap) = andnodecc.(0)
	in
	let (AITT aOut) = n.inputindextype
	and dimclass = ClassRepr.applyTypeMap (IdtMap.find andnodeid allDimclass) andnodefwdmap
	in
	let liveDims = Array.make (Array.length aOut.(0)) false
	in
	Array.iter (fun oldIdx ->
		liveDims.(oldIdx) <- true
	) dataEdgeBM;
	let outpClass = ClassRepr.make (Array.length aOut.(0))
	in
	for i = 0 to (ClassRepr.length dimclass) - 1 do
		ClassRepr.joinClasses outpClass oldEdgeBM.(i) oldEdgeBM.(ClassRepr.getClass dimclass i)
	done;
	let eqDimList = List.filter (fun (x,y) -> x <> y && not (liveDims.(x) && liveDims.(y))) (List.map (fun i -> (ClassRepr.getClass outpClass i, i)) (intfromto 0 ((Array.length aOut.(0)) - 1)))
	in
	if eqDimList = [] then dg else
	let reducDimsNum = List.length eqDimList
	and lostDims = IntSet.of_list (List.map snd eqDimList)
	in
	let survivingDimsNum = (Array.length aOut.(0)) - reducDimsNum
	in
	let equalDimsIxmap = Array.make survivingDimsNum 0
	and outpixt = Array.make survivingDimsNum (NoValue, None)
	in
	let ii = ref 0
	in
	for i = 0 to ((Array.length equalDimsIxmap) - 1) do
		while IntSet.mem !ii lostDims do
			ii := !ii + 1
		done;
		equalDimsIxmap.(i) <- !ii;
		outpixt.(i) <- aOut.(0).(!ii);
		ii := !ii + 1
	done;
	let dimReducer = {
		nkind = nkEqualDims VBoolean eqDimList;
		id = NewName.get ();
		inputs = PortMap.empty;
		inputindextype = n.inputindextype;
		outputindextype = AITT [| outpixt |];
		ixtypemap = IxM [| Some ((), 0, equalDimsIxmap) |];
	}
	in
	let dataDimReducer = { dimReducer with
		nkind = nkEqualDims dataVt eqDimList;
		id = NewName.get ();
	}
	in
	DG.addedge ((IxM [| Some (dataDimReducer.id, 0, equalDimsIxmap) |], NewName.get ()), n.id, PortSingle dataVt) (
	DG.addedge ((IxM [| Some (srcid, 0, dataEdgeBM) |], NewName.get ()), dataDimReducer.id, PortSingle dataVt) (
	DG.addedge ((IxM [| Some (dimReducer.id, 0, equalDimsIxmap) |], NewName.get ()), n.id, PortSingleB) (
	DG.addedge ((IxM [| Some (andnodeid, 0, oldEdgeBM) |], NewName.get ()), dimReducer.id, PortSingle VBoolean) (
	DG.addnode dataDimReducer (
	DG.addnode dimReducer (
	DG.remedge controlEdgeId (
	DG.remedge dataEdgeId dg)))))))
;;

let removeOutputControlDims dg =
	let allDimclass = DG.foldnodes (fun n m -> IdtMap.add n.id (findPotentiallyEqualDims dg n) m) dg IdtMap.empty
	in
	DG.foldnodes (fun n dgcurr -> removeOneOutputControlDims dgcurr n allDimclass) dg dg
;;

let mkSingleOutputPerComp dg n =
	let outSourcePl = ref RLSet.empty
	and outTypePl = ref None
	in
	let numOutputs = DG.nodefoldoutedges dg (fun (_, nout, prt) cnt ->
		if (match prt with PortSingle cval -> (outTypePl := Some cval; true) | _ -> false) &&
			(match nout.nkind.nodeintlbl with NNOutput outsrc -> (outSourcePl := RLSet.union outsrc !outSourcePl; true) | _ -> false) then
			cnt + 1 else cnt
	) n 0
	in
	if (numOutputs < 2) then dg else
	let Some outType = !outTypePl
	and outSource = !outSourcePl
	in
	let (outpNodes, orNodes, dg1) = RLSet.fold (fun src (outCurr, orCurr, dgcurr) ->
		let newOutpNode = {
			nkind = nkOutput outType (RLSet.singleton src);
			id = NewName.get ();
			inputindextype = n.outputindextype;
			outputindextype = n.outputindextype;
			ixtypemap = identityIndexMap () n.outputindextype;
			inputs = PortMap.empty;
		}
		and newOrNode = {
			nkind = nkOr;
			id = NewName.get ();
			inputindextype = n.outputindextype;
			outputindextype = n.outputindextype;
			ixtypemap = identityIndexMap () n.outputindextype;
			inputs = PortMap.empty;
		}
		in
		(RLMap.add src newOutpNode.id outCurr, RLMap.add src newOrNode.id orCurr,
			dgcurr |> DG.addnode newOutpNode |> DG.addnode newOrNode |>
				DG.addedge ((identityIndexMap n.id n.outputindextype, NewName.get ()), newOutpNode.id, PortSingle outType) |>
				DG.addedge ((identityIndexMap newOrNode.id n.outputindextype, NewName.get ()), newOutpNode.id, PortSingleB)
		)
	) outSource (RLMap.empty, RLMap.empty, dg)
	in
	DG.nodefoldoutedges dg (fun ((IxM cc, edgeid), nout, prt) dgcurr ->
		match nout.nkind.nodeintlbl, prt with
			| NNOutput thisSrc, PortSingle _ -> begin
				let Some (_,_, backmap) = cc.(0)
				in
				let cntrNodeIdPl = ref None
				and cntrBackMapPl = ref None
				in
				let () = DG.nodefoldedges (fun ((IxM cc', _), _, prt') () ->
					if prt' = PortSingleB then begin
						let Some (id, _, bm) = cc'.(0)
						in
						cntrNodeIdPl := Some id;
						cntrBackMapPl := Some bm
					end
				) nout ()
				in
				let Some cntrNodeId = !cntrNodeIdPl
				and Some cntrBackMap = !cntrBackMapPl
				and (AITT nouta) = nout.inputindextype
				in
				let cntrNode = DG.findnode cntrNodeId dg
				in
				let (AITT cntrb) = cntrNode.outputindextype
				in
				let invBackMap = Array.make (Array.length nouta.(0)) (-1)
				in
				Array.iteri (fun idx v -> invBackMap.(v) <- idx) backmap;
				let cntrToValDimMap = Array.init (Array.length cntrb.(0)) (fun idx -> invBackMap.(cntrBackMap.(idx)))
				in
				let longOrIxMap = Array.make (Array.length backmap) (-1)
				in
				Array.iteri (fun idx v -> if v <> (-1) then longOrIxMap.(v) <- idx) cntrToValDimMap;
				let dgnext = RLSet.fold (fun src dgxcurr ->
					let longornode = {
						nkind = nkLongOr;
						id = NewName.get ();
						inputindextype = cntrNode.outputindextype;
						outputindextype = n.outputindextype;
						ixtypemap = IxM [| Some ((), 0, longOrIxMap) |];
						inputs = PortMap.empty;
					}
					in
					dgxcurr |> DG.addnode longornode |>
						DG.addedge ((identityIndexMap cntrNodeId longornode.inputindextype, NewName.get ()), longornode.id, PortSingleB) |>
						DG.addedge ((identityIndexMap longornode.id longornode.outputindextype, NewName.get ()), RLMap.find src orNodes, PortUnstrB)
					) thisSrc dgcurr
				in
				DG.remnode nout.id dgnext
			end
			| _,_ -> dgcurr
	) n dg1
;;

let singleOutputPerValue dg =
	DG.foldnodes (fun nold dgcurr ->
		if DG.hasnode nold.id dgcurr then
		begin
			let n = DG.findnode nold.id dgcurr
			in
			mkSingleOutputPerComp dgcurr n
		end else dgcurr
	) dg dg
;;

let findDataEdges dg =
	let res = ref IdtSet.empty
	and combineedges = ref IdtSet.empty
	and processQ = Queue.create ()
	in
	let relevantEdge eid =
		if (IdtSet.mem eid !res) || (IdtSet.mem eid !combineedges) then () else
		(res := IdtSet.add eid !res; Queue.add eid processQ)
	and markCombineEdge eid =
		if (IdtSet.mem eid !res) || (IdtSet.mem eid !combineedges) then () else
		(combineedges := IdtSet.add eid !combineedges; Queue.add eid processQ)
	in
	DG.foldnodes (fun n () ->
		if (match n.nkind.nodeintlbl with NNOutput _ -> true | _ -> false) then
		begin
			DG.nodefoldedges (fun ((_,eid),_,prt) () ->
				if (match prt with PortSingle _ -> true | _ -> false) then
					(res := IdtSet.add eid !res; Queue.add eid processQ)
			) n ()
		end
	) dg ();
	while not (Queue.is_empty processQ) do
		let eid = Queue.take processQ
		in
		let ((IxM cc, _), ntgt, prt) = DG.findedge eid dg
		in
		let Some (srcid, _, _) = cc.(0)
		in
		let nsrc = DG.findnode srcid dg
		in
		match nsrc.nkind.nodeintlbl with
			| NNFilter _ ->
				DG.nodefoldedges (fun ((_,eid'),_,prt) () ->
					if IdtSet.mem eid !res then
					begin
						if prt = PortSingleB then () else relevantEdge eid'
					end
					else if IdtSet.mem eid !combineedges then
					begin
						if prt = PortSingleB then () else markCombineEdge eid'
					end
				) nsrc ()
			| NNLongUpdCombine _ ->
				DG.nodefoldedges (fun ((_,eid'),_,prt) () ->
					if IdtSet.mem eid !res then relevantEdge eid'
					else if IdtSet.mem eid !combineedges then markCombineEdge eid'
				) nsrc ()
			| NNUpdCombine _ ->
				DG.nodefoldedges (fun ((IxM cc,eid'),_,prt) () ->
					let Some (ppid,_,_) = cc.(0)
					in
					let ppn = DG.findnode ppid dg
					in
					if IdtSet.mem eid !combineedges then markCombineEdge eid'
					else if (IdtSet.mem eid !res) then (
						if (match ppn.nkind.nodeintlbl with NNLongUpdCombine _ -> true | _ -> false) then markCombineEdge eid'
						else relevantEdge eid' )
				) nsrc ()
			| NNTuple [("idx",VInteger);("data",_)] ->
				DG.nodefoldedges (fun ((_,eid'),_,prt) () ->
					if IdtSet.mem eid !res then relevantEdge eid'
					else if (IdtSet.mem eid !combineedges) && (prt = PortOperInput 2) then relevantEdge eid'
				) nsrc ()
			| NNITE _ ->
				DG.nodefoldedges (fun ((_,eid'),_,prt) () ->
					if prt <> PortSingleB then relevantEdge eid'
				) nsrc ()
			| _ -> DG.nodefoldedges (fun ((_,eid'),_,_) () -> if IdtSet.mem eid !res then relevantEdge eid') nsrc ()
	done;
	IdtSet.union !res !combineedges
;;

let moveOneLongMergeNode dg oldeid =
	let ((IxM cc,_), ntgt, prt) = DG.findedge oldeid dg
	in
	let Some (nid,_,tgtbackmap) = cc.(0)
	in
	let n = DG.findnode nid dg
	in
	print_string ("Calling moveMerge for edge " ^ (NewName.to_string oldeid) ^ ", going from " ^ (NewName.to_string n.id) ^ " to " ^ (NewName.to_string ntgt.id) ^ "\n");
	if (match n.nkind.nodeintlbl with NNLongMerge _ -> false | _ -> true) then Right false else
	if (match ntgt.nkind.nodeintlbl with NNLongMerge _ -> true | _ -> false) then Right true else 
	begin
	print_string "It is a suitable edge\n";
	let (AITT na) = n.inputindextype
	and (AITT nb) = n.outputindextype
	and (IxM ncc) = n.ixtypemap
	and NNLongMerge vtype = n.nkind.nodeintlbl
	and Some (srcid, _, backmap) = DG.nodefoldedges (fun ((IxM cc,_),_,_) _ ->
		let Some (srcid, useThisEdgeIdLater ,backmap) = cc.(0)
		in
		Some (srcid,useThisEdgeIdLater, backmap)
	) n None
	in
	let Some ((),_,nfwdmap) = ncc.(0)
	in
	let unusedDims = Array.make (Array.length na.(0)) true
	in
	for i = 0 to (Array.length nb.(0)) - 1 do
		unusedDims.(nfwdmap.(i)) <- false
	done;
	let (contractedDims, contractedDimsMap) =
		let res = Array.make ((Array.length na.(0)) - (Array.length nb.(0))) (-1)
		and resdims = Array.make ((Array.length na.(0)) - (Array.length nb.(0))) (VInteger, None)
		and idx = ref 0
		in
		for i = 0 to (Array.length na.(0)) - 1 do
			if unusedDims.(i) then
			begin
				res.(!idx) <- i;
				resdims.(!idx) <- na.(0).(i);
				idx := !idx + 1
			end
		done;
		(resdims, res)
	and revfwdmap =
		let res = Array.make (Array.length na.(0)) (-1)
		in
		for i = 0 to (Array.length nb.(0)) - 1 do
			res.(nfwdmap.(i)) <- i
		done;
		res
	in
	let revcontractedmap =
		let res = Array.make (Array.length na.(0)) (-1)
		in
		for i = 0 to (Array.length contractedDims) - 1 do
			res.(contractedDimsMap.(i)) <- i
		done;
		res
	in
	let (AITT ntgta) = ntgt.inputindextype
	and (AITT ntgtb) = ntgt.outputindextype
	and (IxM ntgtc) = ntgt.ixtypemap
	in
	let Some ((),_,ntfwdmap) = ntgtc.(0)
	in
	let xtgtacomp = Array.append ntgta.(0) contractedDims
	and xtgtbcomp = Array.append ntgtb.(0) contractedDims
	and xtgtccomp = Array.append ntfwdmap (Array.init (Array.length contractedDims) (fun x ->  x + (Array.length ntgta.(0))))
	in
	let xtgt = {
		nkind = ntgt.nkind;
		id = NewName.get ();
		inputs = PortMap.empty;
		inputindextype = AITT [| xtgtacomp |];
		outputindextype = AITT [| xtgtbcomp |];
		ixtypemap = IxM [| Some ((),0,xtgtccomp) |];
	}
	in
	let newmerge = {
		nkind = nkLongMerge (xtgt.nkind.outputtype);
		id = ntgt.id;
		inputs = PortMap.empty;
		inputindextype = AITT [| xtgtbcomp |];
		outputindextype = ntgt.outputindextype;
		ixtypemap = IxM [| Some ((),0, Array.init (Array.length ntgtb.(0)) (fun x -> x)) |];
	}
	in
	let src2xtgtmapcomp =
		let mapsrcidx x =
			let atoldmergea = backmap.(x)
			in
			if unusedDims.(atoldmergea) then
			begin
				let atcontracteddims = revcontractedmap.(atoldmergea)
				in
				atcontracteddims + (Array.length ntgta.(0))
			end
			else
			begin
				let atoldmergeb = revfwdmap.(atoldmergea)
				in
				tgtbackmap.(atoldmergeb)
			end
		in
		Array.init (Array.length backmap) mapsrcidx
	in
	let newedgeid = NewName.get ()
	in
	let dg1 = DG.addedge ((identityIndexMap xtgt.id (AITT [| xtgtbcomp |]), newedgeid),newmerge.id, PortSingle xtgt.nkind.outputtype) (DG.changenode newmerge (DG.addnode xtgt dg))
	in
	let dg2 = DG.nodefoldedges (fun ((IxM icc,ieid), _, iprt) dgx ->
		if ieid = oldeid then
			DG.addedge ((IxM [| Some (srcid, 0, src2xtgtmapcomp) |], ieid), xtgt.id, iprt) dgx
		else
			DG.addedge ((IxM icc, ieid), xtgt.id, iprt) dgx
	) ntgt dg1
	in
	let newdataedges = DG.nodefoldoutedges dg2 (fun ((IxM occ, oeid), onn, oprt) currdataedges ->
		IdtSet.add oeid currdataedges
	) newmerge IdtSet.empty
	in
	print_string ("The new node has id " ^ (NewName.to_string xtgt.id) ^ "\n");
	Left (dg2, newdataedges, newedgeid)
	end
;;

let moveMergeDown dg =
	let dataedges = ref (findDataEdges dg)
	and currdg = ref dg
	and breakLoop = ref false
	and lastRetry = ref None
	in
	let edgeQ = Queue.create ()
	and elemsInQ = ref IdtSet.empty
	in
	let putInQueue eid = if IdtSet.mem eid !elemsInQ then () else
		begin
			Queue.add eid edgeQ;
			elemsInQ := IdtSet.add eid !elemsInQ
		end
	and takeFromQueue () =
		let eid = Queue.take edgeQ
		in
		elemsInQ := IdtSet.remove eid !elemsInQ;
		eid
	in
	IdtSet.iter (fun eid ->
		putInQueue eid
	) !dataedges;
	let checkLoopInvariant () =
		let edgesFollowingLM = IdtSet.filter (fun eid ->
			let ((IxM cc,_),_,_) = DG.findedge eid !currdg
			in
			let Some (srcid,_,_) = cc.(0)
			in
			let srcn = DG.findnode srcid !currdg
			in
			match srcn.nkind.nodeintlbl with NNLongMerge _ -> true | _ -> false
		) !dataedges
		in
		let badEdges = Queue.fold (fun ss eid -> IdtSet.remove eid ss) edgesFollowingLM edgeQ
		in
		IdtSet.iter (fun eid ->
			let ((IxM cc,_),ntgt,_) = DG.findedge eid !currdg
			in
			let Some (srcid,_,_) = cc.(0)
			in
			print_string ("The edge no. " ^ (NewName.to_string eid) ^ " from " ^ (NewName.to_string srcid) ^ " to " ^ (NewName.to_string ntgt.id) ^ " is missing from the queue!\n")
		) badEdges
	in
	while (not (Queue.is_empty edgeQ)) && (not !breakLoop) do
		checkLoopInvariant ();
		let eid = takeFromQueue ()
		in
		print_string ("Take edge no. " ^ (NewName.to_string eid) ^ " from queue\n");
		match moveOneLongMergeNode !currdg eid with
		| Right false -> ()
		| Right true ->
		begin
			match !lastRetry with
			| Some eid' when eid = eid' -> (breakLoop := true)
			| Some eid' -> (putInQueue eid'; print_string "put it back to queue\n")
			| None -> (lastRetry := Some eid; putInQueue eid; print_string ("put it back to queue, start loop detection; there are now " ^ (string_of_int (Queue.length edgeQ)) ^ " edges in the queue\n"))
		end
		| Left (newdg, edgesForQ, newdataedge) ->
		begin
			lastRetry := None;
			IdtSet.iter (fun neid ->
				if IdtSet.mem neid !dataedges then (putInQueue neid; print_string ("Add edge no. " ^ (NewName.to_string neid) ^ " to queue\n"))
			) edgesForQ;
			dataedges := IdtSet.add newdataedge !dataedges;
			currdg := newdg;
			let ((IxM cc,_),_,_) = DG.findedge eid newdg
			in
			let Some (srcid,_,_) = cc.(0)
			in
			let srcn = DG.findnode srcid newdg
			in
			if (match srcn.nkind.nodeintlbl with NNLongMerge _ -> true | _ -> false) then
				(putInQueue eid; print_string ("Adding edge no. " ^ (NewName.to_string eid) ^ " back to the queue\n"))
		end
	done;
	!currdg
;;

let moveOneFilterNode dg oldeid =
	let ((IxM cc,_), ntgt, prt) = DG.findedge oldeid dg
	in
	let Some (nid,_,tgtbackmap) = cc.(0)
	in
	let n = DG.findnode nid dg
	in
	print_string ("Calling moveFilter for edge " ^ (NewName.to_string oldeid) ^ ", going from " ^ (NewName.to_string n.id) ^ " to " ^ (NewName.to_string ntgt.id) ^ "\n");
	if (match n.nkind.nodeintlbl with NNFilter _ -> false | _ -> true) then None else
	if (match ntgt.nkind.nodeintlbl with NNLongUpdCombine _ | NNUpdCombine _ -> true | _ -> false) then None else
	if ntgt.nkind.contracts then None else
	if (match ntgt.nkind.nodeintlbl with NNFilter _ | NNOutput _ -> true | _ -> false) then 
	begin
		print_string "Joining two filters\n";
		let (AITT na) = n.inputindextype
		and (AITT nb) = n.outputindextype
		and (IxM ncc) = n.ixtypemap
		and (Some (srcid, backmap), Some (fltsrcid, fltbackmap)) = DG.nodefoldedges (fun ((IxM cc,_),_,prt) (foundsrc, foundflt) ->
			let Some (srcid, _, backmap) = cc.(0)
			in
			if prt = PortSingleB then (foundsrc, Some (srcid, backmap)) else (Some (srcid, backmap), foundflt)
		) n (None, None)
		and Some (flt2srcid, flt2eid, flt2backmap) = DG.nodefoldedges (fun ((IxM cc,_),_,prt) foundflt ->
			let Some (srcid, flt2eid, backmap) = cc.(0)
			in
			if prt = PortSingleB then Some (srcid, flt2eid, backmap) else foundflt
		) ntgt None
		and vtype =
			match ntgt.nkind.nodeintlbl with
			| NNFilter x -> x
			| NNOutput _ ->
			begin
				let Some x = PortSet.fold (fun prtname res ->
					match prtname with
					| PortSingle y -> Some y
					| _ -> res
				) ntgt.nkind.ports None
				in
				x
			end
		in
		let Some ((),_,nfwdmap) = ncc.(0)
		in
		let revfwdmap =
			let res = Array.make (Array.length na.(0)) (-1)
			in
			for i = 0 to (Array.length nb.(0)) - 1 do
				res.(nfwdmap.(i)) <- i
			done;
			res
		in
		let combNode = {
			nkind = nkAnd;
			id = NewName.get ();
			inputindextype = ntgt.inputindextype;
			outputindextype = ntgt.inputindextype;
			ixtypemap = identityIndexMap () ntgt.inputindextype;
			inputs = PortMap.empty;
		}
		and flt2tgtmap = Array.init (Array.length fltbackmap) (fun x -> tgtbackmap.(revfwdmap.(fltbackmap.(x))))
		and src2tgtmap = Array.init (Array.length backmap) (fun x -> tgtbackmap.(revfwdmap.(backmap.(x))))
		in
		let dg1 =
			DG.addedge ((IxM [| Some (flt2srcid, 0, flt2backmap) |], NewName.get ()), combNode.id, PortStrictB)
			(DG.addedge ((IxM [| Some (fltsrcid, 0, flt2tgtmap) |], NewName.get ()), combNode.id, PortStrictB)
			(DG.addedge ((identityIndexMap combNode.id ntgt.inputindextype, flt2eid), ntgt.id, PortSingleB)
			(DG.addedge ((IxM [| Some (srcid, 0, src2tgtmap) |], oldeid), ntgt.id, PortSingle vtype)
			(DG.addnode combNode dg))))
		in
		Some (Right dg1)
	end
	else 
	begin
	print_string "It is a suitable edge\n";
	let (AITT na) = n.inputindextype
	and (AITT nb) = n.outputindextype
	and (IxM ncc) = n.ixtypemap
	and NNFilter vtype = n.nkind.nodeintlbl
	and (Some (srcid, backmap), Some (fltsrcid, fltbackmap)) = DG.nodefoldedges (fun ((IxM cc,_),_,prt) (foundsrc, foundflt) ->
		let Some (srcid, _, backmap) = cc.(0)
		in
		if prt = PortSingleB then (foundsrc, Some (srcid, backmap)) else (Some (srcid, backmap), foundflt)
	) n (None, None)
	in
	let Some ((),_,nfwdmap) = ncc.(0)
	in
	let revfwdmap =
		let res = Array.make (Array.length na.(0)) (-1)
		in
		for i = 0 to (Array.length nb.(0)) - 1 do
			res.(nfwdmap.(i)) <- i
		done;
		res
	in
	let (AITT ntgta) = ntgt.inputindextype
	and (AITT ntgtb) = ntgt.outputindextype
	and (IxM ntgtc) = ntgt.ixtypemap
	in
	let Some ((),_,ntfwdmap) = ntgtc.(0)
	in
	let xtgtacomp = ntgta.(0)
	and xtgtbcomp = ntgtb.(0)
	and xtgtccomp = ntfwdmap
	in
	let xtgt = {
		nkind = ntgt.nkind;
		id = NewName.get ();
		inputs = PortMap.empty;
		inputindextype = AITT [| xtgtacomp |];
		outputindextype = AITT [| xtgtbcomp |];
		ixtypemap = IxM [| Some ((),0,xtgtccomp) |];
	}
	in
	let newfilter = {
		nkind = nkFilter (xtgt.nkind.outputtype);
		id = ntgt.id;
		inputs = PortMap.empty;
		inputindextype = AITT [| xtgtbcomp |];
		outputindextype = ntgt.outputindextype;
		ixtypemap = IxM [| Some ((),0, Array.init (Array.length ntgtb.(0)) (fun x -> x)) |];
	}
	in
	let src2xtgtmapcomp =
		let mapsrcidx x =
			let atoldmergea = backmap.(x)
			in
			let atoldmergeb = revfwdmap.(atoldmergea)
			in
			tgtbackmap.(atoldmergeb)
		in
		Array.init (Array.length backmap) mapsrcidx
	in
	let newedgeid = NewName.get ()
	and filteringbackmap = Array.init (Array.length fltbackmap) (fun x -> tgtbackmap.(revfwdmap.(fltbackmap.(x))))
	in
	let dg1 = DG.addedge ((IxM [| Some (fltsrcid, 0, filteringbackmap) |], NewName.get ()), newfilter.id, PortSingleB) (DG.addedge ((identityIndexMap xtgt.id (AITT [| xtgtbcomp |]), newedgeid), newfilter.id, PortSingle xtgt.nkind.outputtype) (DG.changenode newfilter (DG.addnode xtgt dg)))
	in
	let dg2 = DG.nodefoldedges (fun ((IxM icc,ieid), _, iprt) dgx ->
		if ieid = oldeid then
			DG.addedge ((IxM [| Some (srcid, 0, src2xtgtmapcomp) |], ieid), xtgt.id, iprt) dgx
		else
			DG.addedge ((IxM icc, ieid), xtgt.id, iprt) dgx
	) ntgt dg1
	in
	let newdataedges = DG.nodefoldoutedges dg2 (fun ((IxM occ, oeid), onn, oprt) currdataedges ->
		IdtSet.add oeid currdataedges
	) newfilter IdtSet.empty
	in
	print_string ("The new node has id " ^ (NewName.to_string xtgt.id) ^ "\n");
	Some (Left (dg2, newdataedges, newedgeid))
	end
;;

let moveFilterDown dg =
	let dataedges = ref (findDataEdges dg)
	and currdg = ref dg
	in
	let edgeQ = Queue.create ()
	and elemsInQ = ref IdtSet.empty
	in
	let putInQueue eid = if IdtSet.mem eid !elemsInQ then () else
		begin
			Queue.add eid edgeQ;
			elemsInQ := IdtSet.add eid !elemsInQ
		end
	and takeFromQueue () =
		let eid = Queue.take edgeQ
		in
		elemsInQ := IdtSet.remove eid !elemsInQ;
		eid
	in
	IdtSet.iter (fun eid ->
		putInQueue eid
	) !dataedges;
	let checkLoopInvariant () =
		let edgesFollowingLM = IdtSet.filter (fun eid ->
			let ((IxM cc,_),_,_) = DG.findedge eid !currdg
			in
			let Some (srcid,_,_) = cc.(0)
			in
			let srcn = DG.findnode srcid !currdg
			in
			match srcn.nkind.nodeintlbl with NNLongMerge _ -> true | _ -> false
		) !dataedges
		in
		let badEdges = Queue.fold (fun ss eid -> IdtSet.remove eid ss) edgesFollowingLM edgeQ
		in
		IdtSet.iter (fun eid ->
			let ((IxM cc,_),ntgt,_) = DG.findedge eid !currdg
			in
			let Some (srcid,_,_) = cc.(0)
			in
			print_string ("The edge no. " ^ (NewName.to_string eid) ^ " from " ^ (NewName.to_string srcid) ^ " to " ^ (NewName.to_string ntgt.id) ^ " is missing from the queue!\n")
		) badEdges
	in
	while (not (Queue.is_empty edgeQ)) do
		(* checkLoopInvariant (); *)
		let eid = takeFromQueue ()
		in
		print_string ("Take edge no. " ^ (NewName.to_string eid) ^ " from queue\n");
		match moveOneFilterNode !currdg eid with
		| None -> ()
		| Some (Right dgnew) ->
		begin
			currdg := dgnew
		end
		| Some (Left (newdg, edgesForQ, newdataedge)) ->
		begin
			IdtSet.iter (fun neid ->
				if IdtSet.mem neid !dataedges then (putInQueue neid; print_string ("Add edge no. " ^ (NewName.to_string neid) ^ " to queue\n"))
			) edgesForQ;
			dataedges := IdtSet.add newdataedge !dataedges;
			currdg := newdg;
			let ((IxM cc,_),_,_) = DG.findedge eid newdg
			in
			let Some (srcid,_,_) = cc.(0)
			in
			let srcn = DG.findnode srcid newdg
			in
			if (match srcn.nkind.nodeintlbl with NNFilter _ -> true | _ -> false) then
				(putInQueue eid; print_string ("Adding edge no. " ^ (NewName.to_string eid) ^ " back to the queue\n"))
		end
	done;
	!currdg
;;

