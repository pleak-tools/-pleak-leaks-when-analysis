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
		let newInputIndices = Array.map (fun _ -> NewName.get ()) a
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

let foldAndsTogether dg =
	let rec makeLongEdge (IxM m) =
		let Some (midid, comp, prt) = m.(0)
		in
		let midn = DG.findnode midid dg
		in
		match midn.nkind.nodeintlbl with
			| NNAnd ->
				DG.nodefoldedges (fun ((cc, _),_,_) ll ->
					let lx = makeLongEdge cc
					in
					(List.map (fun (IxM m') -> composeIxM (IxM m) midid (IxM m')) lx) @ ll
				) midn []
			| _ -> [IxM m]
	in
	DG.foldnodes (fun n dgcurr ->
		match n.nkind.nodeintlbl with
			| NNAnd ->
				DG.nodefoldedges (fun ((cc,eid),tgt,prt) dgnext ->
					let lx = makeLongEdge cc
					in
					List.fold_right (fun cc' dg' -> DG.addedge ((cc', NewName.get ()), tgt.id, prt) dg') lx (DG.remedge eid dgnext)
				) n dgcurr
			| _ -> dgcurr
	) dg dg
;;

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

let simplifyAnd dg n =
	if n.nkind.nodeintlbl <> NNAnd then None else
	let hasFalseInput =
		let foundyet = ref false
		in
		DG.nodefoldedges (fun ((IxM cc,eid),_,_) () ->
			if !foundyet then () else
			let Some (srcid, _, _) = cc.(0)
			in
			let srcn = DG.findnode srcid dg
			in
			foundyet := match srcn.nkind.nodeintlbl with
				| NNFalse -> true
				| _ -> false
		) n ();
		!foundyet
	in
	if hasFalseInput then
	begin
		let nnew = {n with
			inputs = PortMap.empty;
			nkind = nkFalse
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
			match srcn.nkind.nodeintlbl with
				| NNTrue -> (foundTrue := true; DG.remedge eid dgcurr)
				| _ -> dgcurr
		) n dg
		in
		let inpcount = DG.nodefoldedges (fun _ i -> i+1) (DG.findnode n.id simpTrueDg) 0
		in
		let afterCountDg =
			if inpcount = 0 then
				let nnew = {n with
					inputs = PortMap.empty;
					nkind = nkTrue
				}
				in
				(foundTrue := true; DG.changenode nnew simpTrueDg)
			else if inpcount = 1 then
				let nnew = {n with
					inputs = PortMap.empty;
					nkind = nkId VBoolean
				}
				in
				(foundTrue:= true;
				DG.nodefoldedges (fun ((cc,eid),_,_) dgcurr -> DG.addedge ((cc,eid), n.id, PortSingle VBoolean) dgcurr) (DG.findnode n.id simpTrueDg) (DG.changenode nnew simpTrueDg))
			else simpTrueDg
		in
		if !foundTrue then Some afterCountDg else None
	end
;;

let simplifyAddition dg n =
	if n.nkind.nodeintlbl <> NNOperation OPPlus then None else
	if (PortSet.cardinal n.nkind.ports) <> 1 then None else
	let nnew = {n with
		nkind = nkId VInteger;
		inputs = PortMap.empty;
	}
	in
	let dgwid = DG.changenode nnew dg
	in
	let dgnew = DG.nodefoldedges (fun ((cc,eid),_,prt) dgcurr ->
		DG.addedge ((cc, eid), n.id, PortSingle VInteger) dgcurr
	) n dgwid
	in
	Some dgnew
;;

let dontOutputNulls dg n =
	if n.nkind.nodeintlbl <> NNOutput then None else
	let srcidpl = ref None
	in
	DG.nodefoldedges (fun ((IxM cc,eid),_,prt) () ->
		match prt with
			| PortSingle _ ->
				let Some (srcid,_,_) = cc.(0)
				in srcidpl := Some srcid
			| _ -> ()
	) n ();
	let Some srcid = !srcidpl
	in
	let src = DG.findnode srcid dg
	in
	match src.nkind.nodeintlbl with
		| NNOperation (OPNull _) -> Some (DG.remnode n.id dg)
		| _ -> None
;;

let simplifyArithmetic dg =
	TopolSorter.fold (fun nid dgnew ->
		let n = DG.findnode nid dgnew
		in
		let dg1 = match simplifyCoalesce dgnew n with
			| None -> dgnew
			| Some dg' -> dg'
		in
		let n1 = DG.findnode nid dg1
		in
		let dg2 = match simplifyAnd dg1 n1 with
			| None -> dg1
			| Some dg' -> dg'
		in
		let n2 = DG.findnode nid dg2
		in
		let dg3 = match simplifyAddition dg2 n2 with
			| None -> dg2
			| Some dg' -> dg'
		in
		let n3 = DG.findnode nid dg3
		in
		let dg4 = match dontOutputNulls dg3 n3 with
			| None -> dg3
			| Some dg' -> dg'
		in 
		dg4
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

let iseqToDimEq dg = DG.foldnodes (fun nold dgcurr -> iseqToDimEqNode dgcurr (DG.findnode nold.id dgcurr)) dg dg;;

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
end : sig
	type t
	val make : int -> t
	val getClass : t -> int -> int
	val joinClasses : t -> int -> int -> unit
	val length : t -> int
end);;

let reduceOneAndDimension dg n =
	if n.nkind.nodeintlbl <> NNAnd then None else
	let (outpNodeIds, onlyOutputSuccs) = DG.nodefoldoutedges dg (fun ((_,_), tgtn, prt) (currIds, currFlag) ->
		if not currFlag then (IdtSet.empty, false) else
		match tgtn.nkind.nodeintlbl, prt with
			| NNOutput, PortSingleB -> (IdtSet.add tgtn.id currIds, true)
			| _,_ -> (IdtSet.empty, false)
	) n (IdtSet.empty, true)
	in
	if not onlyOutputSuccs then None else
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
			nkind = nkOutput dataVt;
			id = NewName.get ();
			inputindextype = AITT [| thisOutpIxt |];
			outputindextype = AITT [| thisOutpIxt |];
			inputs = PortMap.empty;
			ixtypemap = IxM [| Some ((), 0, Array.init (Array.length thisOutpIxt) (fun x -> x)) |];
		}
		in
(*		DG.addedge ((IxM [| Some (srcid, 0, Array.init (Array.length dataEdgeBM) (fun x -> oldToNewDims.(dataEdgeBM.(x)))) |], NewName.get ()), dataDimReducer.id, PortSingle dataVt) (  *)
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
	if (match n.nkind.nodeintlbl with NNOutput -> false | _ -> true) then dg else
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
	let (AITT aOut) = n.inputindextype
	and dimclass = IdtMap.find andnodeid allDimclass
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

