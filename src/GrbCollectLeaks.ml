open GrbGraphs;;
open GrbCommons;;

let safestringsub s st l =
	if (String.length s) < st + l then "" else String.sub s st l
;;

let rec (oneOfEach : 'a list list -> 'a list list) = function
	| [] -> [[]]
	| l :: ls ->
		let backs = oneOfEach ls
		in
		let rec putInFront xx =
			match xx with
				| [] -> []
				| x :: xs -> (List.map (fun z -> x :: z) backs) @ (putInFront xs)
		in putInFront l
;;

let rec describeDependency dg n =
	match n.nkind.nodeintlbl with
		| NNTakeDim _
		| NNTrue _
		| NNFalse _
		| NNError -> []
		| NNInputExists _
		| NNInput _ -> [n.nkind.nodelabel, "always"]
		| NNOperation OPGeoDist
		| NNOperation OPDiv
		| NNNot
		| NNNotFlip _
		| NNAnd _
		| NNLongOr _
		| NNLongAnd _
		| NNOperation OPCoalesce
		| NNTuple _
		| NNOperation OPPlus ->
			let inpdescs = DG.nodefoldedges (fun ((IxM m,eid),_,prt) dd ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in
				let ddcurr = describeDependency dg ninp
				in
				ddcurr :: dd
			) n []
			in
			let variants = oneOfEach inpdescs
			in
			List.map (fun ll -> let ll1 = List.map fst ll and ll2 = List.map snd ll in (String.concat " and " ll1, String.concat " and " ll2) ) variants
		| NNIsEq ->
			let (inpdescs, inpdeps) = DG.nodefoldedges (fun ((IxM m,eid),_,prt) (ll, dd) ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in
				let ddcurr = describeDependency dg ninp
				in
				((describeCondition dg ninp) :: ll, (List.map snd ddcurr) :: dd )
			) n ([], [])
			in ["Equality of [" ^ (String.concat " and " inpdescs) ^ "]", String.concat " or " (List.map (String.concat " and ") (oneOfEach (List.filter (function [] -> false | _ -> true) inpdeps))) ]
		| NNOperation OPLessThan ->
			let (inpdescs, inpdeps) = DG.nodefoldedges (fun ((IxM m,eid),_,prt) (ll, dd) ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in
				let ddcurr = describeDependency dg ninp
				in
				((prt, describeCondition dg ninp) :: ll, (List.map snd ddcurr) :: dd )
			) n ([], [])
			in
			let smaller = List.assoc (PortOperInput 1) inpdescs
			and larger = List.assoc (PortOperInput 2) inpdescs
			in
			["Whether " ^ smaller ^ " is less than " ^ larger, String.concat " or " (List.map (String.concat " and ") (oneOfEach (List.filter (function [] -> false | _ -> true) inpdeps))) ]
		| NNOperation OPLessEqual ->
			let (inpdescs, inpdeps) = DG.nodefoldedges (fun ((IxM m,eid),_,prt) (ll, dd) ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in
				let ddcurr = describeDependency dg ninp
				in
				((prt, describeCondition dg ninp) :: ll, (List.map snd ddcurr) :: dd )
			) n ([], [])
			in
			let smaller = List.assoc (PortOperInput 1) inpdescs
			and larger = List.assoc (PortOperInput 2) inpdescs
			in
			["Whether " ^ smaller ^ " is less than or equal to " ^ larger, String.concat " or " (List.map (String.concat " and ") (oneOfEach (List.filter (function [] -> false | _ -> true) inpdeps))) ]
		| NNMakeBag _
		| NNAggregate AGMakeBag
		| NNFilter _
		| NNOutput _ ->
			let inputdescPl = ref None
			and controldescPl = ref ""
			in
			DG.nodefoldedges (fun ((IxM m,eid),_,prt) () ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in
				match prt with
					| PortSingleB _ ->
						controldescPl := describeCondition dg ninp
					| PortSingle _ ->
						inputdescPl := Some (describeDependency dg ninp)
			) n ();
			let Some inputdesc = !inputdescPl
			and controldesc = !controldescPl
			in
			List.map (fun (s1,s2) -> (s1, controldesc ^ " and (" ^ s2 ^ ")") ) inputdesc
		| NNSeqNo ->
			let inputdescPl = ref None
			in
			DG.nodefoldedges (fun ((IxM m,eid),_,prt) () ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in
				match prt with
					| PortSingle _ ->
						inputdescPl := Some (describeDependency dg ninp)
					| _ -> ()
			) n ();
			let Some inputdesc = !inputdescPl
			in
			inputdesc
		| NNOperation (OPIntConst _) -> []
		| NNOperation (OPNull _) -> []
		| NNITE _ ->
			let truedescPl = ref None
			and falsedescPl = ref None
			and controldescPl = ref None
			in
			DG.nodefoldedges (fun ((IxM m,eid),_,prt) () ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in
				match prt with
					| PortSingleB _ ->
						controldescPl := Some (describeCondition dg ninp)
					| PortTrue _ ->
						truedescPl := Some (describeDependency dg ninp)
					| PortFalse _ ->
						falsedescPl := Some (describeDependency dg ninp)
			) n ();
			let Some truedesc = !truedescPl
			and Some falsedesc = !falsedescPl
			and Some controldesc = !controldescPl
			in
			let addstatement sToAdd sExisting =
				if sExisting = "" then sToAdd else sToAdd ^ " and " ^ sExisting
			in
			(List.map (fun (s1,s2) -> (addstatement ("[ Whether " ^ controldesc ^ "]") s1, addstatement controldesc s2) ) truedesc) @
			(List.map (fun (s1,s2) -> (addstatement ("[ Whether " ^ controldesc ^ "]") s1, addstatement ("not (" ^ controldesc ^ ")") s2) ) falsedesc)
and describeCondition dg n =
	let collectInputDescs () =
		DG.nodefoldedges (fun ((IxM m,eid),_,prt) ll ->
			let Some (srcid,_,_) = m.(0)
			in
			let ninp = DG.findnode srcid dg
			in
			let ddcurr = describeCondition dg ninp
			in
			PortMap.add prt ddcurr ll
		) n PortMap.empty
	in
	match n.nkind.nodeintlbl with
		| NNDimEq -> ""
		| NNAnd _ ->
			let inpdescs = DG.nodefoldedges (fun ((IxM m,eid),_,prt) ll ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in (describeCondition dg ninp) :: ll
			) n []
			in "All of the following hold: [" ^ (String.concat ", " inpdescs) ^ "]"
		| NNOr _ ->
			let inpdescs = DG.nodefoldedges (fun ((IxM m,eid),_,prt) ll ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in (describeCondition dg ninp) :: ll
			) n []
			in "At least one of the following holds: [" ^ (String.concat ", " inpdescs) ^ "]"
		| NNNot
		| NNNotFlip _ ->
				let inpdescs = DG.nodefoldedges (fun ((IxM m,eid),_,prt) ll ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in (describeCondition dg ninp) :: ll
			) n []
			in "The statement \"" ^ (List.hd inpdescs) ^ "\" does not hold"
		| NNTakeDim _ -> n.nkind.nodelabel
		| NNTrue _ -> "TRUE"
		| NNFalse _ -> "FALSE"
		| NNError -> "ERROR"
		| NNInputExists _ -> n.nkind.nodelabel
		| NNInput _ -> "The value of " ^ (n.nkind.nodelabel)
		| NNOperation OPGeoDist ->
			let desc = collectInputDescs ()
			in
			"The geographic distance between the point with latitude {" ^ (PortMap.find (PortOperInput 1) desc) ^ "} and longitude {" ^ (PortMap.find (PortOperInput 2) desc) ^ "}, and the point with latitude {" ^ (PortMap.find (PortOperInput 3) desc) ^ "} and longitude {" ^ (PortMap.find (PortOperInput 4) desc) ^ "}"
		| NNOperation OPDiv ->
			let desc = collectInputDescs ()
			in
			"The ratio between {" ^ (PortMap.find (PortOperInput 1) desc) ^ "} and {" ^ (PortMap.find (PortOperInput 2) desc) ^ "}"
		| NNOperation OPPlus ->
			let desc = collectInputDescs ()
			in
			"The sum of {" ^ (PortMap.find (PortOperInput 1) desc) ^ "} and {" ^ (PortMap.find (PortOperInput 2) desc) ^ "}"
		| NNIsEq ->
			let inpdescs = DG.nodefoldedges (fun ((IxM m,eid),_,prt) ll ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in (describeCondition dg ninp) :: ll
			) n []
			in "All of the following are equal to each other: [" ^ (String.concat ", " inpdescs) ^ "]"
		| NNOperation OPLessThan ->
			let desc = collectInputDescs ()
			in
			"Whether {" ^ (PortMap.find (PortOperInput 1) desc) ^ "} is smaller than {" ^ (PortMap.find (PortOperInput 2) desc) ^ "}"
		| NNOperation OPLessEqual ->
			let desc = collectInputDescs ()
			in
			"Whether {" ^ (PortMap.find (PortOperInput 1) desc) ^ "} is smaller than or equal to {" ^ (PortMap.find (PortOperInput 2) desc) ^ "}"
		| NNMakeBag _
		| NNAggregate AGMakeBag ->
			let descs = collectInputDescs ()
			and VBag (dims,vt) = n.nkind.outputtype
			in
			"A collection of {" ^ (PortMap.find (PortSingle vt) descs) ^ "} grouped along " ^ (String.concat ", " (List.map fst dims)) (* ^ ", for rows satisfying " ^ (PortMap.find PortSingleB descs) *)
		| NNFilter vt ->
			let descs = collectInputDescs ()
			in
			"The value of {" ^ (PortMap.find (PortSingle vt) descs) ^ "}, only if " ^ (PortMap.find (PortSingleB true) descs) ^ " holds true"
		| NNSeqNo ->
			let descs = collectInputDescs ()
			in
			let bagdescPl = ref None
			in
			PortMap.iter (fun prt d ->
				match prt with
					| PortSingle (VBag _) -> bagdescPl := Some d
					| _ -> ()
			) descs;
			let Some bagdesc = !bagdescPl
			in
			"The sequence number for a value chosen from " ^ bagdesc
		| NNOperation (OPIntConst c) -> string_of_int c
		| NNLongOr isVBoolean ->
			let desc = collectInputDescs ()
			in
			"One of the many {" ^ (PortMap.find (PortSingleB isVBoolean) desc) ^ "} holds"
		| NNLongAnd isVBoolean ->
			let desc = collectInputDescs ()
			in
			"All of the many {" ^ (PortMap.find (PortSingleB isVBoolean) desc) ^ "} hold"
		| NNOperation (OPNull _) -> "NULL"
		| NNOperation OPCoalesce ->
			let desc = collectInputDescs ()
			in
			"The first non-NULL among [" ^ (String.concat ", " (List.map snd (PortMap.bindings desc))) ^ "]"
		| NNTuple _ ->
			let desc = collectInputDescs ()
			in
			"The tuple [" ^ (String.concat ", " (List.map snd (PortMap.bindings desc))) ^ "]"
		| NNITE vt ->
			let desc = collectInputDescs ()
			in
			"If " ^ (PortMap.find (PortSingleB true) desc) ^ " then " ^ (PortMap.find (PortTrue vt) desc) ^ " else " ^ (PortMap.find (PortFalse vt) desc)
		| NNOutput _ -> ""
;;

let describeAllDependencies oc dg =
	DG.foldnodes (fun n () ->
		match n.nkind.nodeintlbl with
			| NNOutput inputDescription ->
				let deps = describeDependency dg n
				in
				output_string oc ("Output no. " ^ (NewName.to_string n.id) ^ " for the input(s) " ^ (String.concat ", " (RLSet.elements inputDescription)));
				List.iter (fun (s1,s2) ->
					output_string oc "\n*. ";
					output_string oc s1;
					output_string oc "\nIF ";
					output_string oc s2
				) deps;
				output_string oc "\n"
			| _ -> ()
	) dg ()
;;

module IdtNameSet = MySet (
struct
	type t = NewName.idtype * string
	let compare = Pervasives.compare
end
);;

type 'a andortree = AOTElem of 'a | AOTAnd of (('a andortree) list) | AOTOr of (('a andortree) list);;

let rec normalizeAOT wholeTree = match wholeTree with
	| AOTElem x -> AOTElem x
	| AOTAnd ll | AOTOr ll ->
		let isAnd = (match wholeTree with AOTAnd _ -> true | _ -> false)
		in
		let llnew = List.map normalizeAOT ll
		in
		let rec flattenLL = function
			| [] -> Some []
			| x :: xs ->
				let flatXSOpt = flattenLL xs
				in
				(match flatXSOpt with
					| None -> None
					| Some flatXS ->
						(match x,wholeTree with
							| AOTAnd inner, AOTAnd _
							| AOTOr inner, AOTOr _ ->
								Some (List.append inner flatXS)
							| AOTOr [], AOTAnd _
							| AOTAnd [], AOTOr _ -> None
							| _,_ -> Some (x :: flatXS)
				))
		in
		let res = (match (flattenLL llnew) with
			| Some x -> 
				let y = List.sort_uniq Pervasives.compare x
				in 
				if (List.length y) = 1 then List.hd y else
				if isAnd then AOTAnd y else AOTOr y
			| None -> if isAnd then AOTOr [] else AOTAnd []
		)
		in res
;;

let rec mapFOnAOT f wholeTree =
	match wholeTree with
		| AOTAnd ll -> AOTAnd (List.map (mapFOnAOT f) ll)
		| AOTOr ll -> AOTOr (List.map (mapFOnAOT f) ll)
		| AOTElem x ->
			let wt = f x
			in
			(match wt with
				| AOTElem _ -> wt
				| _ -> mapFOnAOT f wt
			)
;;

let rec foldOnAOT op_and op_or op_elem = function
	| AOTAnd ll ->
		op_and (List.map (foldOnAOT op_and op_or op_elem) ll)
	| AOTOr ll ->
		op_or (List.map (foldOnAOT op_and op_or op_elem) ll)
	| AOTElem x -> op_elem x
;;

let iterOnAOT on_elem = foldOnAOT (fun _ -> ()) (fun _ -> ()) on_elem;;

let mapOnAOT f = foldOnAOT (fun l -> AOTAnd l) (fun l -> AOTOr l) (fun x -> AOTElem (f x));;

type expWithDims = EWDInput of string * string * (string IdtMap.t)	(* table name, attribute name, dims *)
				 | EWDExists of string * (string IdtMap.t)			(* table name, dims *)
				 | EWDCompute of operationname * expWithDims list
				 | EWDComputeGen of string * expWithDims list
				 | EWDTakeDim of NewName.idtype * string
				 | EWDAggregate of aggregationname * IdtNameSet.t * outputdescdimstype
				 | EWDSeqNo of ((NewName.idtype * string) list) * expWithDims
and outputdescdimstype = {
	outputdims : string IdtMap.t;
	quantifieddims : string IdtMap.t list; (* the head is "exists" *)
	outputthing : expWithDims;
	outputconds : expWithDims andortree;
};;

let rec joinDimLists dl =
	let dlNoNil = List.filter (fun l -> l <> []) dl
	in
	if dlNoNil = [] then [] else
	let fstElem = List.fold_right (fun eleml currm ->
		IdtMap.merge (fun _ x y -> if x = None then y else x) (List.hd eleml) currm
	) dlNoNil IdtMap.empty
	and restElems = joinDimLists (List.map List.tl dlNoNil)
	in
	fstElem :: restElems
;;

let rec dependencyOfAnOutput dg n incomingDimNames =
	if (match n.nkind.nodeintlbl with NNFilter _ | NNOutput _ -> false | _ -> true) then raise (Failure "dependencyOfAnOutput called for non-NNOutput or non-NNFilter node") else
	let srcidpl = ref None
	and cntrlpl = ref None
	and srcidbackmappl = ref None
	and cntrlbackmappl = ref None
	and vtpl = ref None
	and globalDimNames = ref IdtMap.empty
	in
	DG.nodefoldedges (fun ((IxM cc,eid),_,prt) () ->
		match prt with
			| PortSingle vt ->
				let Some (srcid,_,backmap) = cc.(0)
				in (srcidpl := Some srcid; srcidbackmappl := Some backmap; vtpl := Some vt)
			| PortSingleB _ ->
				let Some (srcid,_,backmap) = cc.(0)
				in (cntrlpl := Some srcid; cntrlbackmappl := Some backmap)
	) n ();
	let Some srcid = !srcidpl
	and Some cntrlid = !cntrlpl
	and Some srcbackmap = !srcidbackmappl
	and Some cntrlbackmap = !cntrlbackmappl
	in
	let srcn = DG.findnode srcid dg
	and cntrl = DG.findnode cntrlid dg
	in
	let moveDimRecOverEdge dimrec backmap =
		let respl = ref IntMap.empty
		in
		Array.iteri (fun idx ptr -> respl := IntMap.add idx (IntMap.find ptr dimrec) !respl) backmap;
		!respl
	in
	let moveDimRecInsideNode dimrec fwdmap na0 =
		let isFreshDim = Array.make (Array.length na0) true
		and respl = ref IntMap.empty
		and ndpl = ref IdtMap.empty
		in
		Array.iteri (fun idx ptr ->
			respl := IntMap.add ptr (IntMap.find idx dimrec) !respl;
			isFreshDim.(ptr) <- false
		) fwdmap;
		Array.iteri (fun idx bb -> if bb then begin
			let newdimid = NewName.get ()
			and (_, Some dimname) = na0.(idx)
			in
			ndpl := IdtMap.add newdimid dimname !ndpl;
			respl := IntMap.add idx newdimid !respl
		end ) isFreshDim;
		(!respl, !ndpl)
	in
	let (nadimrec, outdims, exdims) = match incomingDimNames with
		| None -> begin
			let srcdims =
				let (AITT b) = srcn.outputindextype
				in
				Array.mapi (fun idx (_, Some dimname) ->
					let newdimid = NewName.get ()
					in (idx, srcbackmap.(idx), newdimid, dimname)
				) b.(0)
			in
			let outdims = Array.fold_right (fun (_, _, dimid, dimname) m -> IdtMap.add dimid dimname m) srcdims IdtMap.empty
			in
			let (AITT na) = n.inputindextype
			in
			let existdimslocs = Array.make (Array.length na.(0)) true
			in
			Array.iter (fun (_, srcidx, _, _) -> existdimslocs.(srcidx) <- false) srcdims;
			let nadimrecpl = ref (Array.fold_right (fun (_, idx, dimid, _) m -> IntMap.add idx dimid m) srcdims IntMap.empty)
			and exdimspl = ref IdtMap.empty
			in
			Array.iteri (fun idx bb -> if bb then begin
				let newdimid = NewName.get ()
				in
				let (_, Some dimname) = na.(0).(idx)
				in
				exdimspl := IdtMap.add newdimid dimname !exdimspl;
				nadimrecpl := IntMap.add idx newdimid !nadimrecpl
			end ) existdimslocs;
			(!nadimrecpl, outdims, !exdimspl)
			end
		| Some belowDims -> begin
			let (AITT nb) = n.outputindextype
			and (AITT na) = n.inputindextype
			and (AITT sb) = srcn.outputindextype
			and (IxM nixtm) = n.ixtypemap
			in
			let Some ((), _, nfwdmap) = nixtm.(0)
			in
			let (upBelowDims, _) = moveDimRecInsideNode belowDims nfwdmap na.(0)
			in
			let srcBelowDims = moveDimRecOverEdge upBelowDims srcbackmap
			in
			let outAndExDims = IntMap.fold (fun idx dimid mm ->
				let (_, Some dimname) = na.(0).(idx)
				in
				IdtMap.add dimid dimname mm
			) upBelowDims IdtMap.empty
			in
			let exdimspl = ref outAndExDims
			and outdimspl = ref IdtMap.empty
			in
			Array.iter (fun nidx ->
				let dimid = IntMap.find nidx upBelowDims
				in
				exdimspl := IdtMap.remove dimid !exdimspl;
				outdimspl := IdtMap.add dimid (IdtMap.find dimid outAndExDims) !outdimspl
			) srcbackmap;
			(upBelowDims, !outdimspl, !exdimspl)
			end
	in
	globalDimNames := IdtMap.add n.id nadimrec !globalDimNames;
	let rec describeNode n alldims underNot =
		let	(AITT b) = n.outputindextype
		and (AITT a) = n.inputindextype
		in
		let resdims = List.fold_right (fun idx m -> 
			let (_, Some sn) = b.(0).(idx)
			in
			IdtMap.add (IntMap.find idx alldims) sn m
		) (intfromto 0 ((Array.length b.(0)) - 1)) IdtMap.empty
		in
		let (IxM mm) = n.ixtypemap
		in
		let Some ((), _, fwdmap) = mm.(0)
		in
		let (alldimsup, freshnewdims) = moveDimRecInsideNode alldims fwdmap a.(0)
		in
		globalDimNames := IdtMap.add n.id alldimsup !globalDimNames;
		match n.nkind.nodeintlbl with
			| NNTakeDim dimname ->
				let dimid = IntMap.find 0 alldims
				in
				((if underNot && (n.nkind.outputtype = VBoolean) then EWDCompute (OPNot, [EWDTakeDim (dimid, dimname)]) else EWDTakeDim (dimid, dimname)), [])
			| NNInput (tblcolname, vt, _) ->
				let dotindex = String.index tblcolname '.'
				in
				let tblname = String.init dotindex (fun i -> tblcolname.[i])
				and colname = String.init ((String.length tblcolname) - dotindex - 1) (fun i -> tblcolname.[dotindex + 1 + i])
				in
				let rescomp = EWDInput (tblname, colname, resdims)
				in
				((if underNot && (vt = VBoolean) then EWDCompute (OPNot, [rescomp]) else rescomp), [])
			| NNInputExists tablename ->
				((if underNot then EWDCompute (OPNot, [EWDExists (tablename, resdims)]) else EWDExists (tablename, resdims)), [])
			| NNId ->
				let Some res = DG.nodefoldedges (fun ((IxM cc, _), _, _) _ ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let r = describeNode (DG.findnode srcid dg) (moveDimRecOverEdge alldimsup backmap) underNot
					in
					Some r
				) n None
				in res
			| NNAnd _ ->
				let (operands, upwardsdims) = DG.nodefoldedges (fun ((IxM cc, _), _, _) (ll, zz) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let (r1, r2) = describeNode (DG.findnode srcid dg) (moveDimRecOverEdge alldimsup backmap) underNot
					in
					(r1 :: ll, r2 :: zz)
				) n ([], [])
				in
				((EWDCompute ((if underNot then OPOr else OPAnd), operands)), joinDimLists upwardsdims)
			| NNIsEq ->
				let (operands, upwardsdims) = DG.nodefoldedges (fun ((IxM cc, _), _, _) (ll, zz) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let (r1, r2) = describeNode (DG.findnode srcid dg) (moveDimRecOverEdge alldimsup backmap) underNot
					in
					(r1 :: ll, r2 :: zz)
				) n ([], [])
				in
				((if underNot then EWDCompute (OPNot, [EWDCompute (OPIsEq, operands)]) else EWDCompute (OPIsEq, operands)), joinDimLists upwardsdims)
				
			| NNLongOr _ ->
				let Some (r1, r2) = DG.nodefoldedges (fun ((IxM cc, _), _, _) _ ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let r = describeNode (DG.findnode srcid dg) (moveDimRecOverEdge alldimsup backmap) underNot
					in
					Some r
				) n None
				in (r1, joinDimLists [[freshnewdims]; r2])
			| NNMakeBag _
			| NNAggregate AGMakeBag ->
				let Some r = DG.nodefoldedges (fun ((IxM cc, _), _, _) _ ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let srcn = DG.findnode srcid dg
					in
					let srcdowndims = moveDimRecOverEdge alldimsup backmap
					in
					Some (
						let (res, gdns) = dependencyOfAnOutput dg srcn (Some srcdowndims)
						in
						globalDimNames := IdtMap.merge (fun _ x y -> if x = None then y else x) !globalDimNames gdns;
						res
					)
				) n None
				in
				let (AITT b) = n.outputindextype
				in
				((EWDAggregate (AGMakeBag, IntMap.fold (fun idx d s -> let (_, Some dimname) = b.(0).(idx) in IdtNameSet.add (d, dimname) s) alldims IdtNameSet.empty, r)), [ (* freshnewdims *) ])
			| NNSeqNo ->
				let (selectors, Some (r1, r2)) = DG.nodefoldedges (fun ((IxM cc, _), _, prt) (mm, rr) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let srcn = DG.findnode srcid dg
					in
					match prt with
						| PortSeqNo (idx,_,_) ->
							let (_, Some dimname) = a.(0).(backmap.(0))
							in
							(IntMap.add idx (IntMap.find backmap.(0) alldimsup, dimname) mm, rr)
						| _ -> (mm, Some (describeNode srcn (moveDimRecOverEdge alldimsup backmap) underNot) )
				) n (IntMap.empty, None)
				in
				(EWDSeqNo (List.map (fun i -> IntMap.find i selectors) (intfromto 1 (IntMap.cardinal selectors)), r1), r2)
			| NNNot ->
				let Some (r1, r2) = DG.nodefoldedges (fun ((IxM cc, _), _, _) _ ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let r = describeNode (DG.findnode srcid dg) (moveDimRecOverEdge alldimsup backmap) (not underNot)
					in
					Some r
				) n None
				in (r1, if r2 = [] then [] else IdtMap.empty :: r2)
			| NNFilter _ -> raise (Failure "Do not expect to see NNFilter at describeNode")
			| NNOperation opname ->
				let (argdescs, newdims) = DG.nodefoldedges (fun ((IxM cc, _), _, prt) (mm, rr) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let srcn = DG.findnode srcid dg
					in
					match prt with
						| PortOperInput idx ->
							let (r1, r2) = describeNode srcn (moveDimRecOverEdge alldimsup backmap) underNot
							in
							(IntMap.add idx r1 mm, r2 :: rr)
				) n (IntMap.empty, [])
				in
				let rlhalf = EWDCompute (opname, (List.map (fun i -> IntMap.find i argdescs) (intfromto 1 (IntMap.cardinal argdescs))))
				in
				((if n.nkind.outputtype = VBoolean && underNot then EWDCompute (OPNot, [rlhalf]) else rlhalf), joinDimLists newdims)
			| NNAddrGen (place, dimnum, inpnum) ->
				let (argdescs, newdims) = DG.nodefoldedges (fun ((IxM cc, _), _, prt) (mm, rr) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let srcn = DG.findnode srcid dg
					in
					match prt with
						| PortOperInput idx ->
							let (r1, r2) = describeNode srcn (moveDimRecOverEdge alldimsup backmap) underNot
							in
							(IntMap.add idx r1 mm, r2 :: rr)
				) n (IntMap.empty, [])
				in
				let rlhalf = EWDComputeGen ("Addr" ^ (NewName.to_string place) ^ "(" ^ (string_of_int dimnum) ^ ")", (List.map (fun i -> IntMap.find i argdescs) (intfromto 1 (IntMap.cardinal argdescs))))
				in
				((if n.nkind.outputtype = VBoolean && underNot then EWDCompute (OPNot, [rlhalf]) else rlhalf), joinDimLists newdims)
			| NNGeneric (opname, opargnum) ->
				let (argdescs, newdims) = DG.nodefoldedges (fun ((IxM cc, _), _, prt) (mm, rr) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let srcn = DG.findnode srcid dg
					in
					match prt with
						| PortOperInput idx ->
							let (r1, r2) = describeNode srcn (moveDimRecOverEdge alldimsup backmap) underNot
							in
							(IntMap.add idx r1 mm, r2 :: rr)
				) n (IntMap.empty, [])
				in
				let rlhalf = EWDComputeGen (opname, (List.map (fun i -> IntMap.find i argdescs) (intfromto 1 (IntMap.cardinal argdescs))))
				in
				((if n.nkind.outputtype = VBoolean && underNot then EWDCompute (OPNot, [rlhalf]) else rlhalf), joinDimLists newdims)
			| NNSum ->
				let idx = ref 0
				in
				let (argdescs, newdims) = DG.nodefoldedges (fun ((IxM cc, _), _, prt) (mm, rr) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let srcn = DG.findnode srcid dg
					in
					match prt with
						| PortMulti _ ->
							let (r1, r2) = describeNode srcn (moveDimRecOverEdge alldimsup backmap) underNot
							in
							(idx := !idx + 1; (IntMap.add !idx r1 mm, r2 :: rr))
				) n (IntMap.empty, [])
				in
				let rlhalf = EWDCompute (OPPlus, (List.map (fun i -> IntMap.find i argdescs) (intfromto 1 (IntMap.cardinal argdescs))))
				in
				((if n.nkind.outputtype = VBoolean && underNot then EWDCompute (OPNot, [rlhalf]) else rlhalf), joinDimLists newdims)
			| NNAggregate agname ->
				let Some r = DG.nodefoldedges (fun ((IxM cc, _), _, _) _ ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let srcn = DG.findnode srcid dg
					in
					let srcdowndims = moveDimRecOverEdge alldimsup backmap
					in
					Some (
						let (res, gdns) = dependencyOfAnOutput dg srcn (Some srcdowndims)
						in
						globalDimNames := IdtMap.merge (fun _ x y -> if x = None then y else x) !globalDimNames gdns;
						res
					)
				) n None
				in
				let (AITT b) = n.outputindextype
				in
				(EWDAggregate (agname, IntMap.fold (fun idx d s -> let (_, Some dimname) = b.(0).(idx) in IdtNameSet.add (d, dimname) s) alldims IdtNameSet.empty, r), [ (* freshnewdims *) ])
			| NNOutput _ -> raise (Failure "Do not expect to see NNOutput at describeNode")
			| NNOr _ ->
				let (operands, upwardsdims) = DG.nodefoldedges (fun ((IxM cc, _), _, _) (ll, zz) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let (r1, r2) = describeNode (DG.findnode srcid dg) (moveDimRecOverEdge alldimsup backmap) underNot
					in
					(r1 :: ll, r2 :: zz)
				) n ([], [])
				in
				((EWDCompute ((if underNot then OPAnd else OPOr), operands)), joinDimLists upwardsdims)

			| NNTrue _ -> (EWDCompute (OPBoolConst true, []), [])
			| NNFalse _ -> (EWDCompute (OPBoolConst false, []), [])
			| NNError -> raise (Failure "Do not expect to see NNError at describeNode")
			| NNITE _ -> raise (Failure "Do not expect to see NNITE at describeNode")
			| NNDimEq ->
				let (AITT b) = n.outputindextype
				in
				let (_, Some dimname1) = b.(0).(0)
				and (_, Some dimname2) = b.(0).(1)
				in
				let dimid1 = IntMap.find 0 alldims
				and dimid2 = IntMap.find 1 alldims
				in
				let compexp = EWDCompute (OPIsEq, [EWDTakeDim (dimid1, dimname1); EWDTakeDim (dimid2, dimname2)])
				in
				((if underNot then EWDCompute (OPNot, [compexp]) else compexp), [])
			| NNEqualDims _ -> raise (Failure "Do not expect to see NNEqualDims at describeNode")
			| NNTuple svtl ->
				let (argdescs, newdims) = DG.nodefoldedges (fun ((IxM cc, _), _, prt) (mm, rr) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let srcn = DG.findnode srcid dg
					in
					match prt with
						| PortOperInput idx ->
							let (r1, r2) = describeNode srcn (moveDimRecOverEdge alldimsup backmap) underNot
							in
							(IntMap.add idx r1 mm, r2 :: rr)
				) n (IntMap.empty, [])
				in
				let opname = OPTuple (List.map fst svtl)
				in
				let rlhalf = EWDCompute (opname, (List.map (fun i -> IntMap.find i argdescs) (intfromto 1 (IntMap.cardinal argdescs))))
				in
				(rlhalf, joinDimLists newdims)
			| NNProj _ -> raise (Failure "Do not expect to see NNProj at describeNode")
			| NNNumSmaller takeEqual -> (* raise (Failure "Add NNNumSmaller to describeNode") *)
				let (argdescs, newdims) = DG.nodefoldedges (fun ((IxM cc, _), _, prt) (mm, rr) ->
					let Some (srcid, _, backmap) = cc.(0)
					in
					let srcn = DG.findnode srcid dg
					in
					match prt with
						| PortOrder ->
							let (r1, r2) = describeNode srcn (moveDimRecOverEdge alldimsup backmap) underNot
							in
							(IntMap.add 1 r1 mm, r2 :: rr)
						| PortSingle _ ->
							let (r1, r2) = describeNode srcn (moveDimRecOverEdge alldimsup backmap) underNot
							in
							(IntMap.add 2 r1 mm, r2 :: rr)
				) n (IntMap.empty, [])
				in
				(EWDCompute (OPOrder takeEqual, (List.map (fun i -> IntMap.find i argdescs) (intfromto 1 (IntMap.cardinal argdescs)))), joinDimLists newdims)
	in
	let (srcdesc, srcdims) = describeNode srcn (moveDimRecOverEdge nadimrec srcbackmap) false
	in
	let (AITT ca) = cntrl.inputindextype
	and (IxM cm) = cntrl.ixtypemap
	in
	let Some ((), _, cntrlfwdmap) = cm.(0)
	in
	let cbdimrec = moveDimRecOverEdge nadimrec cntrlbackmap
	in
	let cntrdesc = match cntrl.nkind.nodeintlbl with
		| NNAnd _ ->
			let (cadimrec, _) = moveDimRecInsideNode cbdimrec cntrlfwdmap ca.(0)
			in
			DG.nodefoldedges (fun ((IxM cc, _), _, _) ll ->
				let Some (srcid, _, backmap) = cc.(0)
				in
				let r = describeNode (DG.findnode srcid dg) (moveDimRecOverEdge cadimrec backmap) false
				in
				r :: ll
			) cntrl []
		| _ -> [describeNode cntrl cbdimrec false]
	in ({
		outputdims = outdims;
		quantifieddims = joinDimLists (srcdims :: [exdims] :: (List.map snd cntrdesc));
		outputthing = srcdesc;
		outputconds = AOTAnd (List.map (fun (x,_) -> AOTElem x) cntrdesc);
	}, !globalDimNames)
;;

type expWithRows = EWRInput of string * NewName.idtype (* attribute name, table row ID. There's a map from ID-s to table names somewhere *)
				 | EWRExists of NewName.idtype
				 | EWRCompute of operationname * expWithRows list
				 | EWRComputeGen of string * expWithRows list
				 | EWRAggregate of aggregationname * IdtNameSet.t * outputdescrowstype
				 | EWRSeqNo of ((string * NewName.idtype) list) * expWithRows (* list elements: attribute name, table row ID *)
and outputdescrowstype = {
	outputrows : string IdtMap.t; (* maps ID-s to table names *)
	quantifiedrows : string IdtMap.t list; (* the head is "exists" *)
	r_outputthing : expWithRows;
	r_outputconds : expWithRows andortree;
};;

let translateEWD ewd =
	let allRows = ref IdtMap.empty (* codomain: string. Maps a table row ID to the name of the table *)
	and dimToRow = ref IdtMap.empty (* codomain: IdtNameSet.t. Maps a dimension ID to the set of pairs of <table row id, attribute name> *)
	and dimsToRows = Hashtbl.create 10 (* type: string * IdtMap.t --> NewName.idtype. Maps a table name and a set of dimension IDs to the table row ID *)
	and dimsToTable = Hashtbl.create 10 (* type: IdtMap.t --> RLSet.t *)
	in
	let collectAllTableRows () =
		let addTblRow tblname dimset =
			try
				Hashtbl.find dimsToRows (tblname, dimset)
			with Not_found -> begin
				let tblid = NewName.get ()
				in
				allRows := IdtMap.add tblid tblname !allRows;
				IdtMap.iter (fun dimid dimname ->
					let meanings = try IdtMap.find dimid !dimToRow with Not_found -> IdtNameSet.empty
					in
					dimToRow := IdtMap.add dimid (IdtNameSet.add (tblid, dimname) meanings) !dimToRow
				) dimset;
				Hashtbl.add dimsToRows (tblname, dimset) tblid;
				let tblnames =
					if Hashtbl.mem dimsToTable dimset then
						let res = Hashtbl.find dimsToTable dimset
						in
						Hashtbl.remove dimsToTable dimset;
						res
					else RLSet.empty
				in
				Hashtbl.add dimsToTable dimset (RLSet.add tblname tblnames);
				tblid
			end
		in
		let rec collectTableRowsFromEWD ewd =
			collectTableRowsFromExpr ewd.outputthing;
			iterOnAOT collectTableRowsFromExpr ewd.outputconds
		and collectTableRowsFromExpr expr = match expr with
			| EWDInput (tblname, _, dimset) -> ignore (addTblRow tblname dimset)
			| EWDExists (tblname, dimset) -> ignore (addTblRow tblname dimset)
			| EWDCompute (_, ll)
			| EWDComputeGen (_, ll) -> List.iter collectTableRowsFromExpr ll
			| EWDTakeDim _ -> ()
			| EWDAggregate (_, _, ewd) -> collectTableRowsFromEWD ewd
			| EWDSeqNo (_, e) -> collectTableRowsFromExpr e
		in
		collectTableRowsFromEWD ewd
	in
	let checkAllTakeDims () =
		let rec checkTakeDimsEWD ewd =
			checkTakeDimsExpr ewd.outputthing;
			iterOnAOT checkTakeDimsExpr ewd.outputconds
		and checkTakeDimsExpr expr =
			let considerEntry dimid attrname =
				let tblattrset = try IdtMap.find dimid !dimToRow with Not_found -> IdtNameSet.empty
				in
				if IdtNameSet.is_empty tblattrset then
				begin
					let tblid = NewName.get ()
					in
					let tblname = "UNKNOWN" ^ (NewName.to_string tblid)
					in
					allRows := IdtMap.add tblid tblname !allRows;
					dimToRow := IdtMap.add dimid (IdtNameSet.singleton (tblid, attrname)) !dimToRow;
					let idtsingle = IdtMap.singleton dimid attrname
					in
					Hashtbl.add dimsToRows (tblname, idtsingle) tblid;
					let tblnames =
						if Hashtbl.mem dimsToTable idtsingle then
							let res = Hashtbl.find dimsToTable idtsingle
							in
							Hashtbl.remove dimsToTable idtsingle;
							res
						else RLSet.empty
					in
					Hashtbl.add dimsToTable idtsingle (RLSet.add tblname tblnames)
				end else ()
			in
			match expr with
			| EWDInput _ -> ()
			| EWDExists _ -> ()
			| EWDCompute (_, ll)
			| EWDComputeGen (_, ll) -> List.iter checkTakeDimsExpr ll
			| EWDTakeDim (dimid, attrname) -> considerEntry dimid attrname
			| EWDAggregate (_, idns, ewd) -> begin
				IdtNameSet.iter (fun (dimid, attrname) -> considerEntry dimid attrname) idns;
				checkTakeDimsEWD ewd
				end
			| EWDSeqNo (idnl, e) -> begin
				List.iter (fun (dimid, attrname) -> considerEntry dimid attrname) idnl;
				checkTakeDimsExpr e
				end
		in
		checkTakeDimsEWD ewd
	in
	collectAllTableRows ();
	checkAllTakeDims ();
	let dimmapToDimset dimmap = IdtMap.fold (fun k _ s -> IdtSet.add k s) dimmap IdtSet.empty
	in
	let dimParticipateInTables = Hashtbl.fold (fun (tblname, dimset) tblid m ->
		IdtMap.fold (fun dimid dimname mm ->
			let currElems = try IdtMap.find dimid mm with Not_found -> []
			in
			IdtMap.add dimid ((dimmapToDimset dimset, tblid, tblname, dimname) :: currElems) mm
		) dimset m
	) dimsToRows IdtMap.empty
	in
	let rec translateListOfDims consumedDims = function
		| [] -> ([], consumedDims)
		| dimset :: dimsets ->
			let dimlist = IdtMap.bindings dimset
			in
			let rec translateDimList consumedDims = function
				| [] -> (IdtMap.empty, consumedDims)
				| (dimid, dimname) :: dls ->
					if IdtSet.mem dimid consumedDims then translateDimList consumedDims dls else
					let addedConsumedDims = IdtSet.add dimid consumedDims
					in
					let (theRest, finalConsumedDims) = translateDimList addedConsumedDims dls
					in
					let checkList = try IdtMap.find dimid dimParticipateInTables with Not_found -> []
					in
					(
					List.fold_right (fun (_, tblid, tblname, _) thr ->
						IdtMap.add tblid tblname thr
					) (List.filter (fun (ds,_,_,_) -> IdtSet.subset ds addedConsumedDims) checkList) theRest,
					finalConsumedDims)
			in
			let (translatedSet, nextConsumedDims) = translateDimList consumedDims dimlist
			in
			let (finalTranslation, finalConsumedDims) = translateListOfDims nextConsumedDims dimsets
			in
			((translatedSet :: finalTranslation), finalConsumedDims)
	in
	let rec reallyTranslateEWD consumedDims createdTables ewd =
		let (l_outr, consdims1) = translateListOfDims consumedDims [ewd.outputdims]
		in
		let outr = if IdtSet.is_empty consumedDims then 
			RLSet.fold (fun tblname m ->
				try
					IdtMap.add (Hashtbl.find dimsToRows (tblname, IdtMap.empty)) tblname m
				with Not_found -> m
			) (try Hashtbl.find dimsToTable IdtMap.empty with Not_found -> RLSet.empty) (List.hd l_outr)
			else List.hd l_outr
		and (quantr, consdims2) = translateListOfDims consdims1 ewd.quantifieddims
		in
		let newlyConsideredDims = IdtSet.diff consdims2 consumedDims
		and newTableRows = List.fold_right IdtSet.union (List.map dimmapToDimset quantr) (dimmapToDimset outr)
		in
		let tablerows2 = IdtSet.union createdTables newTableRows
		in
		let r_outth = reallyTranslateExpr consdims2 tablerows2 ewd.outputthing
		and r_outcond = mapOnAOT (reallyTranslateExpr consdims2 tablerows2) ewd.outputconds
		in
		let extracond = IdtSet.fold (fun dimid ll ->
			let checkList = IdtMap.find dimid dimParticipateInTables
			in
			let outsideChosen = ref false
			in
			let selectedInps = List.fold_right (fun (_, tblid, tblname, dimname) ll' ->
				if (IdtSet.mem tblid tablerows2) && ((IdtSet.mem tblid newTableRows) || (not !outsideChosen)) then begin
					(if not (IdtSet.mem tblid newTableRows) then outsideChosen := true);
					EWRInput (dimname, tblid) :: ll'
				end else ll'
			) checkList []
			in
			if ((List.length selectedInps) < 2) then ll
			else (EWRCompute (OPIsEq, selectedInps)) :: ll
			(*List.fold_right (fun (_, tblid1, tblname1, dimname1) ll' ->
				List.fold_right (fun (_, tblid2, tblname2, dimname2) ll'' ->
					if (tblid1 <> tblid2) && (IdtSet.mem tblid1 tablerows2) && (IdtSet.mem tblid2 tablerows2) &&
						((IdtSet.mem tblid1 newTableRows) || (IdtSet.mem tblid2 newTableRows)) &&
						((not (IdtSet.mem tblid1 newTableRows)) || (not (IdtSet.mem tblid2 newTableRows)) || ((NewName.to_string tblid1) < (NewName.to_string tblid2))) then
						(EWRCompute (OPIsEq, [EWRInput (dimname1,tblid1); EWRInput (dimname2,tblid2)])) :: ll''
					else ll''
				) checkList ll'
			) checkList ll *)
		) consdims2 []
		in
		let mkAOTNormal whTree =
			let splitComp = function
				| EWRCompute (OPAnd, ll) -> AOTAnd (List.map (fun x -> AOTElem x) ll)
				| EWRCompute (OPOr, ll) -> AOTOr (List.map (fun x -> AOTElem x) ll)
				| otherComp -> AOTElem otherComp
			in
			normalizeAOT (mapFOnAOT splitComp whTree)
		and clearExists whTree =
			let rmExists = function
				| EWRExists _ -> AOTAnd []
				| EWRCompute (OPNot, [EWRExists _]) -> AOTOr []
				| otherComp -> AOTElem otherComp
			in
			normalizeAOT (mapFOnAOT rmExists whTree)
		in {
			outputrows = outr;
			quantifiedrows = quantr;
			r_outputthing = r_outth;
			r_outputconds = clearExists (mkAOTNormal (AOTAnd (r_outcond :: (List.map (fun x -> AOTElem x) extracond))));
		}
	and reallyTranslateExpr consdimspass consrowspass expr = match expr with
		| EWDInput (tblname, attrname, dimset) ->
			let tblid = Hashtbl.find dimsToRows (tblname, dimset)
			in
			EWRInput (attrname, tblid)
		| EWDExists (tblname, dimset) ->
			let tblid = Hashtbl.find dimsToRows (tblname, dimset)
			in
			EWRExists tblid
		| EWDCompute (opname, explist) ->
			let subexps = List.map (reallyTranslateExpr consdimspass consrowspass) explist
			in
			EWRCompute (opname, subexps)
		| EWDComputeGen (opname, explist) ->
			let subexps = List.map (reallyTranslateExpr consdimspass consrowspass) explist
			in
			EWRComputeGen (opname, subexps)
		| EWDTakeDim (dimid, dimname) ->
			let (tblid, dimname') = IdtNameSet.choose (IdtMap.find dimid !dimToRow)
			in
			EWRInput (dimname', tblid)
		| EWDAggregate (agname, remaindims, ewd) -> 
			EWRAggregate (agname, IdtNameSet.map (fun (dimid, dimname) -> IdtNameSet.choose (IdtMap.find dimid !dimToRow)) remaindims, reallyTranslateEWD consdimspass consrowspass ewd)
		| EWDSeqNo (dsl, e) ->
			let e_out = reallyTranslateExpr consdimspass consrowspass e
			and tsl = List.map (fun (dimid, dimname) -> let (x,y) = IdtNameSet.choose (IdtMap.find dimid !dimToRow) in (y,x)) dsl
			in
			EWRSeqNo (tsl, e_out)
	in
	reallyTranslateEWD IdtSet.empty IdtSet.empty ewd
;;
			
(*
let translateEWD ewd =
	let allRows = ref IdtMap.empty
	and dimToRow = ref IdtMap.empty
	and dimsToRows = Hashtbl.create 10
	and noDimTables = ref RLSet.empty
	in
	let addEqToSet extraEQpl tblrow1 attr1 tblrow2 attr2 =
		if (tblrow1 = tblrow2) && (attr1 = attr2) then () else
		let strrow1 = NewName.to_string tblrow1
		and strrow2 = NewName.to_string tblrow2
		in
		let (t1,a1,t2,a2) = if (strrow1 < strrow2) || ((strrow1 = strrow2) && (attr1 < attr2)) then (tblrow1, attr1, tblrow2, attr2) else (tblrow2, attr2, tblrow1, attr1)
		in
		let v1 = IdtMap.finddef RLMap.empty t1 !extraEQpl
		in
		let v2 = RLMap.finddef IdtNameSet.empty a1 v1
		in
		extraEQpl := IdtMap.add t1 (RLMap.add a1 (IdtNameSet.add (t2, a2) v2) v1) !extraEQpl
	in
	let dimsetToTblrow extraEQpl tblname dimset =
		let res = try
			Hashtbl.find dimsToRows (tblname, dimset)
			with Not_found -> begin
				let tblid = NewName.get ()
				in
				allRows := IdtMap.add tblid tblname !allRows;
				Hashtbl.add dimsToRows (tblname, dimset) tblid;
				(if IdtMap.is_empty dimset then noDimTables := RLSet.add tblname !noDimTables);
				IdtMap.iter (fun dimid dimname ->
					let meanings = try IdtMap.find dimid !dimToRow with Not_found -> IdtNameSet.empty
					in
					dimToRow := IdtMap.add dimid (IdtNameSet.add (tblid, dimname) meanings) !dimToRow
				) dimset;
				tblid
			end
		in
		IdtMap.iter (fun dimid dimname ->
			let meanings = try IdtMap.find dimid !dimToRow with Not_found -> IdtNameSet.empty
			in
			IdtNameSet.iter (fun (t2,a2) ->
				addEqToSet extraEQpl t2 a2 res dimname
			) meanings
		) dimset;
		res
	in
	let dimsetToRowset prevRows dimset =
		let rowset0 = IdtMap.fold (fun dimid dimname m ->
			let (tblid, _) = IdtNameSet.choose (IdtMap.find dimid !dimToRow)
			in
			let tblname = IdtMap.find tblid !allRows
			in
			IdtMap.add tblid tblname m
		) dimset IdtMap.empty
		in
		IdtSet.fold (fun existRow m ->
			if IdtMap.mem existRow m then IdtMap.remove existRow m else m
		) prevRows rowset0
	and dimmapToDimset dimmap = IdtMap.fold (fun k _ s -> IdtSet.add k s) dimmap IdtSet.empty
	in
	let dimidToTblattr dimid dimname =
		try
			IdtNameSet.choose (IdtMap.find dimid !dimToRow)
		with Not_found -> begin
			let tblid = NewName.get ()
			in
			let tblname = "UNKNOWN_" ^ (NewName.to_string tblid)
			in
			allRows := IdtMap.add tblid tblname !allRows;
			dimToRow := IdtMap.add dimid (IdtNameSet.singleton (tblid, dimname)) !dimToRow;
			Hashtbl.add dimsToRows (tblname, IdtMap.singleton dimid dimname) tblid;
			(tblid, dimname)
		end
	in
	let rec collectTableRowsEWD ewd =
		let extraEQs = ref IdtMap.empty
		in
		collectTableRowsExpr extraEQs ewd.outputthing;
		List.iter (collectTableRowsExpr extraEQs) ewd.outputconds
	and collectTableRowsExpr extraEQpl = function
		| EWDInput (tblname, _, dimset) -> ignore (dimsetToTblrow extraEQpl tblname dimset)
		| EWDExists (tblname, dimset) -> ignore (dimsetToTblrow extraEQpl tblname dimset)
		| EWDCompute (_, ll) -> List.iter (collectTableRowsExpr extraEQpl) ll
		| EWDTakeDim _ -> ()
		| EWDAggregate (_, _, ewd) -> collectTableRowsEWD ewd
		| EWDSeqNo (_, e) -> collectTableRowsExpr extraEQpl e
	in
	let rec realTranslateEWD ewd fromOutside =
		let extraEQs = ref IdtMap.empty
		in
		let (r_ot, rtblinds) = realTranslateExpr extraEQs ewd.outputthing
		and r_ocndsAndInds = List.map (realTranslateExpr extraEQs) ewd.outputconds
		in
		let r_ocnds = List.map fst r_ocndsAndInds
		and r_cndtblinds = List.map snd r_ocndsAndInds
		in
		let orows =
			let orowsalways = dimsetToRowset IdtSet.empty ewd.outputdims
			in if fromOutside then
				RLSet.fold (fun tblname m ->
					let tblid = Hashtbl.find dimsToRows (tblname, IdtMap.empty)
					in
					IdtMap.add tblid tblname m
				) !noDimTables orowsalways
			else orowsalways
		in
		let qrows =
			let prevrows = ref (dimmapToDimset orows)
			in List.map (fun ds -> 
				let res = dimsetToRowset !prevrows ds
				in
				prevrows := IdtSet.union !prevrows (dimmapToDimset res);
				res
			) ewd.quantifieddims
		in
		let r_ocnds' = IdtMap.fold (fun t1 sm ll ->
			RLMap.fold (fun a1 ta2set ll' ->
				IdtNameSet.fold (fun (t2, a2) ll'' ->
					let compexp = EWRCompute (OPIsEq, [EWRInput (a1,t1); EWRInput (a2,t2)])
					in compexp :: ll''
				) ta2set ll'
			) sm ll
		) !extraEQs []
		in {
			outputrows = orows;
			quantifiedrows = qrows;
			r_outputthing = r_ot;
			r_outputconds = List.append r_ocnds r_ocnds';
		}
	and realTranslateExpr extraEQpl = function
		| EWDInput (tblname, attrname, dimset) ->
			let tblid = dimsetToTblrow extraEQpl tblname dimset
			in
			(EWRInput (attrname, tblid), [IdtMap.singleton tblid tblname])
		| EWDExists (tblname, dimset) ->
			let tblid = dimsetToTblrow extraEQpl tblname dimset
			in
			(EWRExists tblid, [IdtMap.singleton tblid tblname])
		| EWDCompute (opname, explist) ->
			let subexpconvs = List.map (realTranslateExpr extraEQpl) explist
			in
			let subexpewr = List.map fst subexpconvs
			and subexpsrts_pre = joinDimLists (List.map snd subexpconvs)
			in
			let subexpsrts = if opname = OPNot then IdtMap.empty :: subexpsrts_pre else subexpsrts_pre
			in
			(EWRCompute (opname, subexpewr), subexpsrts)
		| EWDTakeDim (dimid, dimname) ->
			let (tblid, tblname) = dimidToTblattr dimid dimname
			in
			(EWRInput (dimname, tblid),  [IdtMap.empty])
		| EWDAggregate (agname, remaindims, ewd) -> 
			(EWRAggregate (agname, IdtNameSet.map (fun (dimid, dimname) -> dimidToTblattr dimid dimname) remaindims, realTranslateEWD ewd false), [IdtMap.empty])
		| EWDSeqNo (dsl, e) ->
			let (e_out, dims_out) = realTranslateExpr extraEQpl e
			in
			let dsl_out = List.map (fun (dimid, dimname) -> let (x,y) = dimidToTblattr dimid dimname in (y,x)) dsl
			and dims2_out = List.fold_right (fun (dimid, dimname) m -> let (x,y) = dimidToTblattr dimid dimname in IdtMap.add x y m) dsl IdtMap.empty
			in
			(EWRSeqNo (dsl_out, e_out), joinDimLists [[dims2_out]; dims_out])
	in
	collectTableRowsEWD ewd;
	realTranslateEWD ewd true
;;
*)

let output_ewr oc ewr =
	let ftr = Format.formatter_of_out_channel oc
	and shortIDs = Hashtbl.create 10
	and nextID = ref 1
	in
	Format.pp_set_max_boxes ftr 0;
	let rowDesc allTbls tblid =
		let tblname = IdtMap.find tblid allTbls
		in
		let tblShortId =
			try
				Hashtbl.find shortIDs tblid
			with Not_found ->
				(let res = !nextID
				in
				nextID := res + 1;
				Hashtbl.add shortIDs tblid res;
				res)
		in
		tblname ^ "_" ^ (string_of_int tblShortId)
	in
	let attrDesc allTbls tblid attrname = (rowDesc allTbls tblid) ^ "." ^ attrname
	in
	let outputListofSmthWithSep argList elemPrinter separatorPrinter =
		let numargs = List.length argList
		in
		List.iteri (fun idx oneArg ->
			elemPrinter oneArg;
			if idx < (numargs - 1) then separatorPrinter () else ()
		) argList
	in
	let outputListofSmth argList elemPrinter =
		outputListofSmthWithSep argList elemPrinter (fun () -> Format.pp_print_string ftr ","; Format.pp_print_space ftr ())
	in
	let rec outputAOT argTree elemPrinter =
		match argTree with
			| AOTElem x -> elemPrinter x
			| AOTAnd ll -> begin
				Format.pp_print_string ftr "{";
				Format.pp_print_space ftr ();
				Format.pp_open_box ftr 2;
				outputListofSmthWithSep ll (fun y -> outputAOT y elemPrinter)
					(fun () -> Format.pp_print_space ftr (); Format.pp_print_string ftr "AND"; Format.pp_print_space ftr ());
				Format.pp_print_space ftr ();
				Format.pp_close_box ftr ();
				Format.pp_print_string ftr "}"
			end
			| AOTOr ll -> begin
				Format.pp_print_string ftr "{";
				Format.pp_print_space ftr ();
				Format.pp_open_box ftr 2;
				outputListofSmthWithSep ll (fun y -> outputAOT y elemPrinter)
					(fun () -> Format.pp_print_space ftr (); Format.pp_print_string ftr "OR"; Format.pp_print_space ftr ());
				Format.pp_print_space ftr ();
				Format.pp_close_box ftr ();
				Format.pp_print_string ftr "}"
			end
	in
	let rec doOutputEWR oldTables ewr =
		let allTables = IdtMap.merge (fun _ x y -> if x = None then y else x)
			(List.fold_right (fun oneMap currMap ->
				IdtMap.merge (fun _ x y -> if x = None then y else x) oneMap currMap
			) ewr.quantifiedrows ewr.outputrows) oldTables
		in
		Format.pp_open_box ftr 2;
			Format.pp_print_string ftr "Output for row(s):";
			Format.pp_print_space ftr ();
			Format.pp_open_box ftr 2;
				outputListofSmth (IdtMap.bindings ewr.outputrows) (fun (tblid, _) -> Format.pp_print_string ftr (rowDesc allTables tblid));
			Format.pp_close_box ftr ();
			Format.pp_print_space ftr ();
			if (ewr.quantifiedrows <> []) && (List.hd ewr.quantifiedrows <> IdtMap.empty) then
			begin
				Format.pp_print_string ftr "IF";
				Format.pp_print_break ftr 0 1;
				List.iteri (fun idx oneDimSet ->
					Format.pp_open_box ftr 2;
					Format.pp_print_string ftr (if (idx mod 2) = 0 then "Exist(s):" else "For all:");
					Format.pp_print_space ftr ();
					Format.pp_open_box ftr 2;
					outputListofSmth (IdtMap.bindings oneDimSet) (fun (tblid, _) -> Format.pp_print_string ftr (rowDesc allTables tblid));
					Format.pp_close_box ftr ();
					Format.pp_print_space ftr ();
				) ewr.quantifiedrows;
				List.iter (fun _ -> Format.pp_close_box ftr ()) ewr.quantifiedrows;
			end;
			Format.pp_print_break ftr 0 1;
			Format.pp_print_string ftr "Output expression:";
			Format.pp_print_space ftr ();
			doOutputExpr allTables ewr.r_outputthing;
			Format.pp_print_space ftr ();
			Format.pp_print_break ftr 0 1;
			Format.pp_print_string ftr "If the following holds:";
			Format.pp_print_space ftr ();
			outputAOT ewr.r_outputconds	(fun r_ot -> doOutputExpr allTables r_ot);
		Format.pp_close_box ftr ()
	and doOutputExpr allTbls = function
		| EWRInput (attrname, tblid) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr (attrDesc allTbls tblid attrname);
			Format.pp_close_box ftr ()
		end
		| EWRExists tblid -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr ("E?(" ^ (rowDesc allTbls tblid) ^ ")" );
			Format.pp_close_box ftr ()
		end
		| EWRCompute (opname, arglist) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr (string_of_opname opname); (if arglist <> [] then
				begin
					Format.pp_print_string ftr "(";
					Format.pp_print_cut ftr ();
					outputListofSmth arglist (doOutputExpr allTbls);
					Format.pp_print_cut ftr ();
					Format.pp_print_string ftr ")"
				end);
			Format.pp_close_box ftr ()
			end
		| EWRComputeGen (opname, arglist) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr opname; (if arglist <> [] then
				begin
					Format.pp_print_string ftr "(";
					Format.pp_print_cut ftr ();
					outputListofSmth arglist (doOutputExpr allTbls);
					Format.pp_print_cut ftr ();
					Format.pp_print_string ftr ")"
				end);
			Format.pp_close_box ftr ()
			end
		| EWRAggregate (aggrname, remaindims, ewr) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr (string_of_aggrname aggrname);
				Format.pp_print_string ftr "{";
				Format.pp_print_cut ftr ();
				(if not (IdtNameSet.is_empty remaindims) then begin
					outputListofSmth (IdtNameSet.elements remaindims) (fun (tblid, attrname) -> Format.pp_print_string ftr (attrDesc allTbls tblid attrname));
				end);
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr "}[";
				Format.pp_print_space ftr ();
				doOutputEWR allTbls ewr;
				Format.pp_print_space ftr ();
				Format.pp_print_string ftr "]";
			Format.pp_close_box ftr ()
			end
		| EWRSeqNo (attrtblnames, insideexp) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr "SeqNo{";
				Format.pp_print_cut ftr ();
				(if attrtblnames <> [] then begin
					outputListofSmth attrtblnames (fun (attrname, tblid) -> Format.pp_print_string ftr (attrDesc allTbls tblid attrname));
				end);
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr "}(";
				Format.pp_print_cut ftr ();
				doOutputExpr allTbls insideexp;
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr ")";
			Format.pp_close_box ftr ()
			end
	in
	doOutputEWR IdtMap.empty ewr;
	Format.pp_print_break ftr 0 1;
	Format.pp_print_flush ftr ();
;;

let rec permutations ll =
	let ins_all_positions x l =  
	  let rec aux prev acc = function
	    | [] -> (prev @ [x]) :: acc |> List.rev
	    | hd::tl as l -> aux (prev @ [hd]) ((prev @ [x] @ l) :: acc) tl
	  in
	  aux [] [] l
	in
	match ll with
	  | [] -> [[]]
	  | x::[] -> [[x]]
	  | x::xs -> List.fold_left (fun acc p -> acc @ ins_all_positions x p ) [] (permutations xs)
;;


let output_ewr_to_graph oc ewr =
	let accGr = List.fold_right (fun (tblname, attrname) mm ->
		let s = try RLMap.find tblname mm with Not_found -> RLSet.empty
		in
		RLMap.add tblname (RLSet.add attrname s) mm
	) RAInput.access_granted RLMap.empty
	in
	let isAttrPrivate tblname attrname =
		if ((String.length tblname) >= 7) && ((String.uppercase (safestringsub tblname 0 7)) = "UNKNOWN") then false else
		let s = try RLMap.find tblname accGr with Not_found -> RLSet.empty
		in
		not (RLSet.mem attrname s)
	in
	let rec compareEWRs idEquiv ewr1 ewr2 = match ewr1, ewr2 with
		| EWRInput (s1,id1), EWRInput (s2,id2) -> (s1 = s2) && (idEquiv id1 id2)
		| EWRExists id1, EWRExists id2 -> idEquiv id1 id2
		| EWRCompute (op1, ll1), EWRCompute (op2, ll2) -> (op1 = op2) && ((List.length ll1) = List.length ll2) && (List.for_all2 (compareEWRs idEquiv) (List.sort Pervasives.compare ll1) (List.sort Pervasives.compare ll2))
		| EWRComputeGen (op1, ll1), EWRComputeGen (op2, ll2) -> (op1 = op2) && ((List.length ll1) = List.length ll2) && (List.for_all2 (compareEWRs idEquiv) (List.sort Pervasives.compare ll1) (List.sort Pervasives.compare ll2))
		| EWRSeqNo (sidl1, c1), EWRSeqNo (sidl2, c2) -> (compareEWRs idEquiv c1 c2) && (List.for_all2 (fun (s1,id1) (s2,id2) -> (s1 = s2) && (idEquiv id1 id2)) sidl1 sidl2)
		| EWRAggregate (ag1, ins1, od1), EWRAggregate (ag2, ins2, od2) ->
			let res =
			(ag1 = ag2) &&
			(List.exists (fun insl2 -> List.for_all2 (fun (id1,s1) (id2,s2) -> (s1 = s2) && (idEquiv id1 id2)) (IdtNameSet.elements ins1) insl2) (permutations (IdtNameSet.elements ins2))) &&
			((List.length od1.quantifiedrows) = (List.length od2.quantifiedrows)) &&
			(IdtMap.cardinal od1.outputrows = IdtMap.cardinal od2.outputrows) &&
			(List.for_all2 (fun m1 m2 -> IdtMap.cardinal m1 = IdtMap.cardinal m2) od1.quantifiedrows od2.quantifiedrows) &&
			(
				let or1l = IdtMap.bindings od1.outputrows
				and qr1ll = List.map IdtMap.bindings od1.quantifiedrows
				and or2lp = permutations (IdtMap.bindings od2.outputrows)
				and qr2lpl = List.map (fun x -> permutations (IdtMap.bindings x)) od2.quantifiedrows
				in
				List.exists (fun or2l ->
					let idEqN1 id1 id2 = (idEquiv id1 id2) || (List.exists2 (fun (ix1,s1) (ix2,s2) -> (ix1 = id1) && (ix2 = id2) && (s1 = s2)) or1l or2l)
					in
					let rec selectElem currIdEq currQR1ll currQR2lpl = match currQR1ll, currQR2lpl with
						| [], [] -> (compareEWRs currIdEq od1.r_outputthing od2.r_outputthing) && (compareEWRAOTs currIdEq od1.r_outputconds od2.r_outputconds)
						| (z1::z1s), (z2p::z2ps) -> List.exists (fun z2 ->
							let nextIdEq id1 id2 = (currIdEq id1 id2) || (List.exists2 (fun (ix1,s1) (ix2,s2) -> (ix1 = id1) && (ix2 = id2) && (s1 = s2)) z1 z2)
							in
							selectElem nextIdEq z1s z2ps
						) z2p
					in
					selectElem idEqN1 qr1ll qr2lpl
				) or2lp
			)
			in
			res
		| _,_ -> false	
	and compareEWRAOTs idEquiv aot1 aot2 = match aot1, aot2 with
		| AOTAnd ll1, AOTAnd ll2 -> List.for_all2 (compareEWRAOTs idEquiv) ll1 ll2
		| AOTOr ll1, AOTOr ll2 -> List.for_all2 (compareEWRAOTs idEquiv) ll1 ll2
		| AOTElem e1, AOTElem e2 -> compareEWRs idEquiv e1 e2
		| _, _ -> false
	in
	let ewridtbl = Hashtbl.create 10
	and rowidtbl = Hashtbl.create 10
	and nidprivtbl = Hashtbl.create 10
	in
	let getRowId rid =
		try
			(Hashtbl.find rowidtbl rid, true)
		with Not_found -> begin
			let nid = NewName.get ()
			in
			Hashtbl.add rowidtbl rid nid;
			(nid, false)
		end
	and getEWRId ewr =
		let phid = Hashtbl.fold (fun ewr' ewid res ->
			match res with
				| Some _ -> res
				| None -> if compareEWRs (=) ewr ewr' then Some ewid else None
		) ewridtbl None
		in
		match phid with
			| Some x -> (x, true)
			| None -> (
				let nid = NewName.get ()
				in
				Hashtbl.add ewridtbl ewr nid;
				(nid, false))
	in
	output_string oc "digraph {\n";
	let dotnodeid x = "v_" ^ (NewName.to_string x)
	and subgrstart x = "subgraph cluster_" ^ (NewName.to_string x)
	in
	let collectAttributeUses ewstr rowsOfInterest =
		let mkAddition tblid attrname roi =
			try
				let s = IdtMap.find tblid roi
				in
				IdtMap.add tblid (RLSet.add attrname s) roi
			with Not_found -> roi
		in
		let rec cau_ewr ewr roi = match ewr with
			| EWRInput (attrname, tblid) -> mkAddition tblid attrname roi
			| EWRExists _ -> roi
			| EWRCompute (_, ll) 
			| EWRComputeGen (_, ll) -> List.fold_right cau_ewr ll roi
			| EWRAggregate (_, remaindims, ewrstr) -> 
				let roi' = IdtNameSet.fold (fun (tblid, attrname) roicurr ->
					mkAddition tblid attrname roicurr
				) remaindims roi
				in
				cau_struct ewrstr roi'
			| EWRSeqNo (stridl, upewr) ->
				let roi' = List.fold_right (fun (attrname, tblid) roicurr ->
					mkAddition tblid attrname roicurr
				) stridl roi
				in
				cau_ewr upewr roi'
		and cau_aotewr aot roi = match aot with
			| AOTElem e -> cau_ewr e roi
			| AOTAnd ll | AOTOr ll -> List.fold_right cau_aotewr ll roi
		and cau_struct ewrstr roi =
			cau_ewr ewrstr.r_outputthing (cau_aotewr ewrstr.r_outputconds roi)
		in
		let roi = IdtSet.fold (fun nid m -> IdtMap.add nid RLSet.empty m) rowsOfInterest IdtMap.empty
		in
		cau_struct ewstr roi
	in
	let rec doOutputEWR ewr =
		let (nid, alreadyIn) = getEWRId ewr
		in
		if alreadyIn then nid else
		(begin
			match ewr with
			| EWRInput (attrname, tblid) -> raise (Failure "doOutputEWR with EWRInput: we should never come to this place")
			| EWRExists _ -> Hashtbl.add nidprivtbl nid false
			| EWRCompute (_, ll)
			| EWRComputeGen (_, ll) ->
				let upl = List.map doOutputEWR ll
				in
				let uplpriv = List.map (Hashtbl.find nidprivtbl) upl
				in
				let nidispriv =
					let res = List.fold_right (||) uplpriv false
					in
					Hashtbl.add nidprivtbl nid res; res
				in
				let nodelbl, numberinps = ( match ewr with | EWRCompute (opname, _) -> (match opname with
					| OPPlus -> "+", false
					| OPNeg -> "-", false
					| OPMult -> "*", false
					| OPIsEq -> "=", false
					| OPLessThan -> "\\<", true
					| OPLessEqual -> "&#8804;", true
					| OPGreaterThan -> "\\>", true
					| OPGreaterEqual -> "&#8805;", true
					| OPAnd -> "AND", false
					| OPOr -> "OR", false
					| OPNot -> "NOT", false
					| OPDiv -> "&#247;", true
					| OPIntConst c -> (string_of_int c), false
					| OPStringConst s -> s, false
					| OPRealConst ff -> (string_of_float ff), false
					| OPBoolConst bb -> (string_of_bool bb), false
					| OPNull _ -> "NULL", false
					| OPGeoDist -> "&#916;", true
					| OPCeiling -> "ceil", false
					| OPCoalesce -> "coalesce", true
					| OPITE -> "?:", true
					| OPTuple strl -> ("[" ^ (String.concat "," strl) ^"]"), true
					| OPProject prname -> ("&#960;" ^ prname), false
					| OPOrder takeEqual -> ("CNT(" ^ (if takeEqual then "LE" else "LT") ^ ")"), true
				)
					| EWRComputeGen (opnamestr, _) -> opnamestr, true
				)
				in
				(
					output_string oc ((dotnodeid nid) ^ " [shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=red" else "filled") ^ " label=\"" ^ nodelbl ^ "\" fillcolor=white];\n");
					List.iteri (fun ifx upid ->
						output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid nid));
						let upidpriv = Hashtbl.find nidprivtbl upid
						in
						if (numberinps || upidpriv) then
						begin
							output_string oc " [";
							(if numberinps then output_string oc ("label=" ^ (string_of_int (ifx+1)) ^ " "));
							(if upidpriv then output_string oc "style=bold color=red");
							output_string oc "]"
						end;
						output_string oc ";\n"
					) upl
				)
			| EWRAggregate (agn, remaindims, ewstr) ->
				let nodelbl = string_of_aggrname agn
				in
				let insideid = doOutputStruct ewstr false
				and groupids = List.map (fun (tblid, attrname) -> doOutputEWR (EWRInput (attrname, tblid))) (IdtNameSet.elements remaindims)
				in
				let groupprivs = List.map (Hashtbl.find nidprivtbl) groupids
				in
				let gbidispriv = List.fold_right (||) groupprivs false
				in
				let nidispriv = gbidispriv || (Hashtbl.find nidprivtbl insideid)
				in
				let gbid = NewName.get ()
				in
				(
					Hashtbl.add nidprivtbl nid nidispriv;
					output_string oc ((dotnodeid gbid) ^ " [shape=box style=" ^ (if gbidispriv then "\"filled,bold\" color=red" else "filled") ^ " label=\"GROUP BY\" fillcolor=white];\n");
					output_string oc ((dotnodeid nid) ^ " [shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=red" else "filled") ^ " label=\"" ^ nodelbl ^ "\" fillcolor=white];\n");
					output_string oc ((dotnodeid gbid) ^ " -> " ^ (dotnodeid nid) ^ (if gbidispriv then "[style=bold color=red]" else "") ^ ";\n");
					output_string oc ((dotnodeid insideid) ^ " -> " ^ (dotnodeid nid) ^ (if Hashtbl.find nidprivtbl insideid then " [style=bold color=red]" else "") ^ ";\n");
					List.iter (fun upid ->
						output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid gbid) ^ (if Hashtbl.find nidprivtbl upid then " [style=bold color=red]" else "") ^ ";\n")
					) groupids
				)
			| EWRSeqNo (stridl, upewr) ->
				let upid = doOutputEWR upewr
				and groupids = List.map (fun (attrname, tblid) -> doOutputEWR (EWRInput (attrname, tblid))) stridl
				and keyid = NewName.get ()
				in
				let keyispriv = List.fold_right (||) (List.map (Hashtbl.find nidprivtbl) groupids) false
				and upispriv = Hashtbl.find nidprivtbl upid
				in
				let nidispriv = upispriv || keyispriv
				in
				(
					Hashtbl.add nidprivtbl nid nidispriv;
					output_string oc ((dotnodeid keyid) ^ " [shape=box style=" ^ (if keyispriv then "\"filled,bold\" color=red" else "filled") ^ " label=\"KEY\" fillcolor=white];\n");
					output_string oc ((dotnodeid nid) ^ " [shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=red" else "filled") ^ " label=\"SeqNo\" fillcolor=white];\n");
					output_string oc ((dotnodeid keyid) ^ " -> " ^ (dotnodeid nid) ^ (if keyispriv then " [style=bold color=red]" else "") ^ ";\n");
					output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid nid) ^ (if upispriv then " [style=bold color=red]" else "") ^ ";\n");
					List.iteri (fun idx gid ->
						output_string oc ((dotnodeid gid) ^ " -> " ^ (dotnodeid keyid) ^ " [label=" ^ (string_of_int (idx+1)) ^ (if Hashtbl.find nidprivtbl gid then " style=bold color=red" else "") ^ "];\n")
					) groupids
				)
		end;
		nid)
	and doOutputAOTEWR aot = match aot with
		| AOTElem x -> doOutputEWR x
		| AOTAnd ll | AOTOr ll ->
			let upl = List.map doOutputAOTEWR ll
			in
			let nid = NewName.get ()
			and nidispriv = List.fold_right (||) (List.map (Hashtbl.find nidprivtbl) upl) false
			in
			Hashtbl.add nidprivtbl nid nidispriv;
			output_string oc ((dotnodeid nid) ^ "[shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=red" else "filled") ^ " label=\"" ^ (match aot with AOTAnd _ -> "AND" | _ -> "OR") ^ "\" fillcolor=white];\n");
			List.iter (fun upid ->
				output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid nid) ^ (if Hashtbl.find nidprivtbl upid then " [style=bold color=red]" else "") ^ ";\n");
			) upl;
			nid
	and doOutputStruct ewstr atBeginning =
		let getIdtSet m = IdtSet.of_list (List.map fst (IdtMap.bindings m))
		in
		let interestingRows = List.fold_right (fun m s -> IdtSet.union (getIdtSet m) s) ewstr.quantifiedrows (getIdtSet ewstr.outputrows)
		in
		let existAttrs = collectAttributeUses ewstr interestingRows
		in
		(if (not atBeginning) then
		begin
			let thrid = NewName.get ()
			in
			output_string oc ("subgraph cluster_" ^ (NewName.to_string thrid) ^ " {\n style=filled;\nfillcolor=cyan\n\n")
		end);
		let drawRowIds0 = IdtMap.mapi (fun k s -> doOutputRow atBeginning true k s (IdtMap.find k existAttrs)) ewstr.outputrows
		in
		let (drawRowIds,_) = List.fold_left (fun (m,bb) qrows -> (IdtMap.mapi (fun k s -> doOutputRow false bb k s (IdtMap.find k existAttrs)) qrows, not bb)) (drawRowIds0, true) ewstr.quantifiedrows
		in
		let resid = doOutputEWR ewstr.r_outputthing
		and condid = doOutputAOTEWR ewstr.r_outputconds
		in
		let nid = NewName.get ()
		in
		let resispriv = Hashtbl.find nidprivtbl resid
		and condispriv = Hashtbl.find nidprivtbl condid
		in
		let nidispriv = resispriv || condispriv
		in
		Hashtbl.add nidprivtbl nid nidispriv;
		output_string oc ((dotnodeid nid) ^ "[shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=red" else "filled") ^ " label=\"Filter\" fillcolor=" ^ (if atBeginning then "blue" else "white") ^ "];\n");
		output_string oc ((dotnodeid resid) ^ " -> " ^ (dotnodeid nid) ^ " [label=1" ^ (if resispriv then " style=bold color=red" else "") ^ "];\n");
		output_string oc ((dotnodeid condid) ^ " -> " ^ (dotnodeid nid) ^ " [label=2" ^ (if condispriv then " style=bold color=red" else "") ^ "];\n");
		(if (not atBeginning) then
		begin
			output_string oc ("}\n")
		end);
		nid
	and doOutputRow isFinalOut isExists rid tbln attrset =
		let (oid, alreadyIn) = getRowId rid
		in
		if alreadyIn then oid
		else
		begin
			output_string oc ((subgrstart oid) ^ " {\n  style=filled;\n  label=\"" ^ tbln ^ "\";\n  fillcolor=" ^ (if isFinalOut then "red" else if isExists then "yellow" else "green") ^";\n");
				RLSet.iter (fun attrname ->
					let (nid,_) = getEWRId (EWRInput (attrname, rid))
					in
					let nidispriv = isAttrPrivate tbln attrname
					in
					Hashtbl.add nidprivtbl nid nidispriv;
					output_string oc ("  " ^ (dotnodeid nid) ^ " [shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=red" else "filled") ^ " label=\"" ^ attrname ^ "\" fillcolor=white];\n")
				) attrset;
			output_string oc "}\n";
			oid
		end
	in
	ignore (doOutputStruct ewr true);
	output_string oc "}\n"
;;

let output_ewr_to_graph_without_deps oc ewr =
	let rec compareEWRs idEquiv ewr1 ewr2 = match ewr1, ewr2 with
		| EWRInput (s1,id1), EWRInput (s2,id2) -> (s1 = s2) && (idEquiv id1 id2)
		| EWRExists id1, EWRExists id2 -> idEquiv id1 id2
		| EWRCompute (op1, ll1), EWRCompute (op2, ll2) -> (op1 = op2) && ((List.length ll1) = List.length ll2) && (List.for_all2 (compareEWRs idEquiv) (List.sort Pervasives.compare ll1) (List.sort Pervasives.compare ll2))
		| EWRComputeGen (op1, ll1), EWRComputeGen (op2, ll2) -> (op1 = op2) && ((List.length ll1) = List.length ll2) && (List.for_all2 (compareEWRs idEquiv) (List.sort Pervasives.compare ll1) (List.sort Pervasives.compare ll2))
		| EWRSeqNo (sidl1, c1), EWRSeqNo (sidl2, c2) -> (compareEWRs idEquiv c1 c2) && (List.for_all2 (fun (s1,id1) (s2,id2) -> (s1 = s2) && (idEquiv id1 id2)) sidl1 sidl2)
		| EWRAggregate (ag1, ins1, od1), EWRAggregate (ag2, ins2, od2) ->
			let res =
			(ag1 = ag2) &&
			(List.exists (fun insl2 -> List.for_all2 (fun (id1,s1) (id2,s2) -> (s1 = s2) && (idEquiv id1 id2)) (IdtNameSet.elements ins1) insl2) (permutations (IdtNameSet.elements ins2))) &&
			((List.length od1.quantifiedrows) = (List.length od2.quantifiedrows)) &&
			(IdtMap.cardinal od1.outputrows = IdtMap.cardinal od2.outputrows) &&
			(List.for_all2 (fun m1 m2 -> IdtMap.cardinal m1 = IdtMap.cardinal m2) od1.quantifiedrows od2.quantifiedrows) &&
			(
				let or1l = IdtMap.bindings od1.outputrows
				and qr1ll = List.map IdtMap.bindings od1.quantifiedrows
				and or2lp = permutations (IdtMap.bindings od2.outputrows)
				and qr2lpl = List.map (fun x -> permutations (IdtMap.bindings x)) od2.quantifiedrows
				in
				List.exists (fun or2l ->
					let idEqN1 id1 id2 = (idEquiv id1 id2) || (List.exists2 (fun (ix1,s1) (ix2,s2) -> (ix1 = id1) && (ix2 = id2) && (s1 = s2)) or1l or2l)
					in
					let rec selectElem currIdEq currQR1ll currQR2lpl = match currQR1ll, currQR2lpl with
						| [], [] -> (compareEWRs currIdEq od1.r_outputthing od2.r_outputthing) && (compareEWRAOTs currIdEq od1.r_outputconds od2.r_outputconds)
						| (z1::z1s), (z2p::z2ps) -> List.exists (fun z2 ->
							let nextIdEq id1 id2 = (currIdEq id1 id2) || (List.exists2 (fun (ix1,s1) (ix2,s2) -> (ix1 = id1) && (ix2 = id2) && (s1 = s2)) z1 z2)
							in
							selectElem nextIdEq z1s z2ps
						) z2p
					in
					selectElem idEqN1 qr1ll qr2lpl
				) or2lp
			)
			in
			res
		| _,_ -> false	
	and compareEWRAOTs idEquiv aot1 aot2 = match aot1, aot2 with
		| AOTAnd ll1, AOTAnd ll2 -> List.for_all2 (compareEWRAOTs idEquiv) ll1 ll2
		| AOTOr ll1, AOTOr ll2 -> List.for_all2 (compareEWRAOTs idEquiv) ll1 ll2
		| AOTElem e1, AOTElem e2 -> compareEWRs idEquiv e1 e2
		| _, _ -> false
	in
	let ewridtbl = Hashtbl.create 10
	and rowidtbl = Hashtbl.create 10
	in
	let getRowId rid =
		try
			(Hashtbl.find rowidtbl rid, true)
		with Not_found -> begin
			let nid = NewName.get ()
			in
			Hashtbl.add rowidtbl rid nid;
			(nid, false)
		end
	and getEWRId ewr =
		let phid = Hashtbl.fold (fun ewr' ewid res ->
			match res with
				| Some _ -> res
				| None -> if compareEWRs (=) ewr ewr' then Some ewid else None
		) ewridtbl None
		in
		match phid with
			| Some x -> (x, true)
			| None -> (
				let nid = NewName.get ()
				in
				Hashtbl.add ewridtbl ewr nid;
				(nid, false))
	in
	output_string oc "digraph {\n";
	let dotnodeid x = "v_" ^ (NewName.to_string x)
	and subgrstart x = "subgraph cluster_" ^ (NewName.to_string x)
	in
	let collectAttributeUses ewstr rowsOfInterest =
		let mkAddition tblid attrname roi =
			try
				let s = IdtMap.find tblid roi
				in
				IdtMap.add tblid (RLSet.add attrname s) roi
			with Not_found -> roi
		in
		let rec cau_ewr ewr roi = match ewr with
			| EWRInput (attrname, tblid) -> mkAddition tblid attrname roi
			| EWRExists _ -> roi
			| EWRCompute (_, ll) 
			| EWRComputeGen (_, ll) -> List.fold_right cau_ewr ll roi
			| EWRAggregate (_, remaindims, ewrstr) -> 
				let roi' = IdtNameSet.fold (fun (tblid, attrname) roicurr ->
					mkAddition tblid attrname roicurr
				) remaindims roi
				in
				cau_struct ewrstr roi'
			| EWRSeqNo (stridl, upewr) ->
				let roi' = List.fold_right (fun (attrname, tblid) roicurr ->
					mkAddition tblid attrname roicurr
				) stridl roi
				in
				cau_ewr upewr roi'
		and cau_aotewr aot roi = match aot with
			| AOTElem e -> cau_ewr e roi
			| AOTAnd ll | AOTOr ll -> List.fold_right cau_aotewr ll roi
		and cau_struct ewrstr roi =
			cau_ewr ewrstr.r_outputthing (cau_aotewr ewrstr.r_outputconds roi)
		in
		let roi = IdtSet.fold (fun nid m -> IdtMap.add nid RLSet.empty m) rowsOfInterest IdtMap.empty
		in
		cau_struct ewstr roi
	in
	let rec doOutputEWR ewr =
		let (nid, alreadyIn) = getEWRId ewr
		in
		if alreadyIn then nid else
		(begin
			match ewr with
			| EWRInput (attrname, tblid) -> raise (Failure "doOutputEWR with EWRInput: we should never come to this place")
			| EWRExists _ -> ()
			| EWRCompute (_, ll)
			| EWRComputeGen (_, ll) ->
				let upl = List.map doOutputEWR ll
				in
				let nodelbl, numberinps = ( match ewr with | EWRCompute (opname, _) -> (match opname with
					| OPPlus -> "+", false
					| OPNeg -> "-", false
					| OPMult -> "*", false
					| OPIsEq -> "=", false
					| OPLessThan -> "\\<", true
					| OPLessEqual -> "&#8804;", true
					| OPGreaterThan -> "\\>", true
					| OPGreaterEqual -> "&#8805;", true
					| OPAnd -> "AND", false
					| OPOr -> "OR", false
					| OPNot -> "NOT", false
					| OPDiv -> "&#247;", true
					| OPIntConst c -> (string_of_int c), false
					| OPStringConst s -> s, false
					| OPRealConst ff -> (string_of_float ff), false
					| OPBoolConst bb -> (string_of_bool bb), false
					| OPNull _ -> "NULL", false
					| OPGeoDist -> "&#916;", true
					| OPCeiling -> "ceil", false
					| OPCoalesce -> "coalesce", true
					| OPITE -> "?:", true
					| OPTuple strl -> ("[" ^ (String.concat "," strl) ^"]"), true
					| OPProject prname -> ("&#960;" ^ prname), false
					| OPOrder takeEqual -> ("CNT(" ^ (if takeEqual then "LE" else "LT") ^ ")"), true
				)
					| EWRComputeGen (opnamestr, _) -> opnamestr, true
				)
				in
				(
					output_string oc ((dotnodeid nid) ^ " [shape=box style=filled label=\"" ^ nodelbl ^ "\" fillcolor=white];\n");
					List.iteri (fun ifx upid ->
						output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid nid));
						(if numberinps then output_string oc (" [label=" ^ (string_of_int (ifx+1)) ^ "]"));
						output_string oc ";\n"
					) upl
				)
			| EWRAggregate (agn, remaindims, ewstr) ->
				let nodelbl = string_of_aggrname agn
				in
				let insideid = doOutputStruct ewstr false
				and groupids = List.map (fun (tblid, attrname) -> doOutputEWR (EWRInput (attrname, tblid))) (IdtNameSet.elements remaindims)
				in
				let gbid = NewName.get ()
				in
				(
					output_string oc ((dotnodeid gbid) ^ " [shape=box style=filled label=\"GROUP BY\" fillcolor=white];\n");
					output_string oc ((dotnodeid nid) ^ " [shape=box style=filled label=\"" ^ nodelbl ^ "\" fillcolor=white];\n");
					output_string oc ((dotnodeid gbid) ^ " -> " ^ (dotnodeid nid) ^ ";\n");
					output_string oc ((dotnodeid insideid) ^ " -> " ^ (dotnodeid nid) ^ ";\n");
					List.iter (fun upid ->
						output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid gbid) ^ ";\n")
					) groupids
				)
			| EWRSeqNo (stridl, upewr) ->
				let upid = doOutputEWR upewr
				and groupids = List.map (fun (attrname, tblid) -> doOutputEWR (EWRInput (attrname, tblid))) stridl
				and keyid = NewName.get ()
				in
				(
					output_string oc ((dotnodeid keyid) ^ " [shape=box style=filled label=\"KEY\" fillcolor=white];\n");
					output_string oc ((dotnodeid nid) ^ " [shape=box style=filled label=\"SeqNo\" fillcolor=white];\n");
					output_string oc ((dotnodeid keyid) ^ " -> " ^ (dotnodeid nid) ^ ";\n");
					output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid nid) ^ ";\n");
					List.iteri (fun idx gid ->
						output_string oc ((dotnodeid gid) ^ " -> " ^ (dotnodeid keyid) ^ " [label=" ^ (string_of_int (idx+1)) ^ "];\n")
					) groupids
				)
		end;
		nid)
	and doOutputAOTEWR aot = match aot with
		| AOTElem x -> doOutputEWR x
		| AOTAnd ll | AOTOr ll ->
			let upl = List.map doOutputAOTEWR ll
			in
			let nid = NewName.get ()
			in
			output_string oc ((dotnodeid nid) ^ "[shape=box style=filled label=\"" ^ (match aot with AOTAnd _ -> "AND" | _ -> "OR") ^ "\" fillcolor=white];\n");
			List.iter (fun upid ->
				output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid nid) ^ ";\n");
			) upl;
			nid
	and doOutputStruct ewstr atBeginning =
		let getIdtSet m = IdtSet.of_list (List.map fst (IdtMap.bindings m))
		in
		let interestingRows = List.fold_right (fun m s -> IdtSet.union (getIdtSet m) s) ewstr.quantifiedrows (getIdtSet ewstr.outputrows)
		in
		let existAttrs = collectAttributeUses ewstr interestingRows
		in
		(if (not atBeginning) then
		begin
			let thrid = NewName.get ()
			in
			output_string oc ("subgraph cluster_" ^ (NewName.to_string thrid) ^ " {\n style=filled;\nfillcolor=cyan\n\n")
		end);
		let drawRowIds0 = IdtMap.mapi (fun k s -> doOutputRow atBeginning true k s (IdtMap.find k existAttrs)) ewstr.outputrows
		in
		let (drawRowIds,_) = List.fold_left (fun (m,bb) qrows -> (IdtMap.mapi (fun k s -> doOutputRow false bb k s (IdtMap.find k existAttrs)) qrows, not bb)) (drawRowIds0, true) ewstr.quantifiedrows
		in
		let resid = doOutputEWR ewstr.r_outputthing
		and condid = doOutputAOTEWR ewstr.r_outputconds
		in
		let nid = NewName.get ()
		in
		output_string oc ((dotnodeid nid) ^ "[shape=box label=\"Filter\" fillcolor=" ^ (if atBeginning then "blue style=filled" else "white style=filled") ^ "];\n");
		output_string oc ((dotnodeid resid) ^ " -> " ^ (dotnodeid nid) ^ " [label=1];\n");
		output_string oc ((dotnodeid condid) ^ " -> " ^ (dotnodeid nid) ^ " [label=2];\n");
		(if (not atBeginning) then
		begin
			output_string oc ("}\n")
		end);
		nid
	and doOutputRow isFinalOut isExists rid tbln attrset =
		let (oid, alreadyIn) = getRowId rid
		in
		if alreadyIn then oid
		else
		begin
			output_string oc ((subgrstart oid) ^ " {\n  style=filled;\n  label=\"" ^ tbln ^ "\";\n  fillcolor=" ^ (if isFinalOut then "red" else if isExists then "yellow" else "green") ^";\n");
				RLSet.iter (fun attrname ->
					let (nid,_) = getEWRId (EWRInput (attrname, rid))
					in
					output_string oc ("  " ^ (dotnodeid nid) ^ " [shape=box style=filled label=\"" ^ attrname ^ "\" fillcolor=white];\n")
				) attrset;
			output_string oc "}\n";
			oid
		end
	in
	ignore (doOutputStruct ewr true);
	output_string oc "}\n"
;;

let output_ewd oc ewd =
	let ftr = Format.formatter_of_out_channel oc
	in
	Format.pp_set_max_boxes ftr 0;
	let rowDesc allDims tblid =
		let tblname = IdtMap.find tblid allDims
		in
		tblname ^ "_" ^ (NewName.to_string tblid)
	in
	let attrDesc allTbls tblid attrname = (rowDesc allTbls tblid) ^ "." ^ attrname
	in
	let outputListofSmthWithSep argList elemPrinter separatorPrinter =
		let numargs = List.length argList
		in
		List.iteri (fun idx oneArg ->
			elemPrinter oneArg;
			if idx < (numargs - 1) then separatorPrinter () else ()
		) argList
	in
	let rec outputAOT argTree elemPrinter =
		match argTree with
			| AOTElem x -> elemPrinter x
			| AOTAnd ll -> begin
				Format.pp_print_string ftr "{";
				Format.pp_print_space ftr ();
				Format.pp_open_box ftr 2;
				outputListofSmthWithSep ll (fun y -> outputAOT y elemPrinter)
					(fun () -> Format.pp_print_space ftr (); Format.pp_print_string ftr "AND"; Format.pp_print_space ftr ());
				Format.pp_print_space ftr ();
				Format.pp_close_box ftr ();
				Format.pp_print_string ftr "}"
			end
			| AOTOr ll -> begin
				Format.pp_print_string ftr "{";
				Format.pp_print_space ftr ();
				Format.pp_open_box ftr 2;
				outputListofSmthWithSep ll (fun y -> outputAOT y elemPrinter)
					(fun () -> Format.pp_print_space ftr (); Format.pp_print_string ftr "OR"; Format.pp_print_space ftr ());
				Format.pp_print_space ftr ();
				Format.pp_close_box ftr ();
				Format.pp_print_string ftr "}"
			end
	in
	let outputListofSmth argList elemPrinter =
		outputListofSmthWithSep argList elemPrinter (fun () -> Format.pp_print_string ftr ","; Format.pp_print_space ftr ())
	in
	let outputDimList dims =
		Format.pp_print_string ftr "<";
		Format.pp_print_cut ftr ();
		outputListofSmth (IdtMap.bindings dims) (fun (dimid, dimname) -> Format.pp_print_string ftr dimname; Format.pp_print_string ftr (NewName.to_string dimid));
		Format.pp_print_cut ftr ();
		Format.pp_print_string ftr ">"
	in
	let rec doOutputEWD oldDims ewd =
		let allIDs = IdtMap.merge (fun _ x y -> if x = None then y else x)
			(List.fold_right (fun oneMap currMap ->
				IdtMap.merge (fun _ x y -> if x = None then y else x) oneMap currMap
			) ewd.quantifieddims ewd.outputdims) oldDims
		in
		Format.pp_open_box ftr 2;
			Format.pp_print_string ftr "Output for row(s):";
			Format.pp_print_space ftr ();
			Format.pp_open_box ftr 2;
				outputListofSmth (IdtMap.bindings ewd.outputdims) (fun (tblid, _) -> Format.pp_print_string ftr (rowDesc allIDs tblid));
			Format.pp_close_box ftr ();
			Format.pp_print_space ftr ();
			if (ewd.quantifieddims <> []) && (List.hd ewd.quantifieddims <> IdtMap.empty) then
			begin
				Format.pp_print_string ftr "IF";
				Format.pp_print_break ftr 0 1;
				List.iteri (fun idx oneDimSet ->
					Format.pp_open_box ftr 2;
					Format.pp_print_string ftr (if (idx mod 2) = 0 then "Exist(s):" else "For all:");
					Format.pp_print_space ftr ();
					outputListofSmth (IdtMap.bindings oneDimSet) (fun (tblid, _) -> Format.pp_print_string ftr (rowDesc allIDs tblid))
				) ewd.quantifieddims;
				List.iter (fun _ -> Format.pp_close_box ftr ()) ewd.quantifieddims;
			end;
			Format.pp_print_break ftr 0 1;
			Format.pp_print_string ftr "Output expression:";
			Format.pp_print_space ftr ();
			doOutputExpr allIDs ewd.outputthing;
			Format.pp_print_break ftr 0 1;
			Format.pp_print_string ftr "If the following holds:";
			Format.pp_print_space ftr ();
			outputAOT ewd.outputconds (fun r_ot -> doOutputExpr allIDs r_ot);
		Format.pp_close_box ftr ()
	and doOutputExpr allTbls = function
		| EWDInput (tblname, attrname, tblid) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr tblname;
				outputDimList tblid;
				Format.pp_print_string ftr ".";
				Format.pp_print_string ftr attrname;
			Format.pp_close_box ftr ()
		end
		| EWDExists (tblname, tblid) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr "E?(";
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr tblname;
				outputDimList tblid;
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr ")";
			Format.pp_close_box ftr ()
		end
		| EWDCompute (opname, arglist) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr (string_of_opname opname); (if arglist <> [] then
				begin
					Format.pp_print_string ftr "(";
					Format.pp_print_cut ftr ();
					outputListofSmth arglist (doOutputExpr allTbls);
					Format.pp_print_cut ftr ();
					Format.pp_print_string ftr ")"
				end);
			Format.pp_close_box ftr ()
			end
		| EWDComputeGen (opname, arglist) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr opname; (if arglist <> [] then
				begin
					Format.pp_print_string ftr "(";
					Format.pp_print_cut ftr ();
					outputListofSmth arglist (doOutputExpr allTbls);
					Format.pp_print_cut ftr ();
					Format.pp_print_string ftr ")"
				end);
			Format.pp_close_box ftr ()
			end
		| EWDTakeDim (dimid, attrname) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr "TD(";
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr attrname;
				Format.pp_print_string ftr (NewName.to_string dimid);
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr ")";
			Format.pp_close_box ftr ()
			end
		| EWDAggregate (aggrname, remaindims, ewdinner) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr (string_of_aggrname aggrname);
				Format.pp_print_string ftr "{";
				Format.pp_print_cut ftr ();
				(if not (IdtNameSet.is_empty remaindims) then begin
					outputListofSmth (IdtNameSet.elements remaindims) (fun (tblid, attrname) -> Format.pp_print_string ftr attrname; Format.pp_print_string ftr (NewName.to_string tblid));
				end);
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr "}[";
				Format.pp_print_space ftr ();
				doOutputEWD allTbls ewdinner;
				Format.pp_print_space ftr ();
				Format.pp_print_string ftr "]";
			Format.pp_close_box ftr ()
			end
		| EWDSeqNo (attrtblnames, insideexp) -> begin
			Format.pp_open_box ftr 2;
				Format.pp_print_string ftr "SeqNo{";
				Format.pp_print_cut ftr ();
				(if attrtblnames <> [] then begin
					outputListofSmth attrtblnames (fun (tblid, attrname) -> Format.pp_print_string ftr attrname; Format.pp_print_string ftr (NewName.to_string tblid));
				end);
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr "}(";
				Format.pp_print_cut ftr ();
				doOutputExpr allTbls insideexp;
				Format.pp_print_cut ftr ();
				Format.pp_print_string ftr ")";
			Format.pp_close_box ftr ()
			end
	in
	doOutputEWD IdtMap.empty ewd;
	Format.pp_print_break ftr 0 1;
	Format.pp_print_flush ftr ();
;;

type studyleakstype =
	SLTAnd of studyleakstype list |
	SLTOr of studyleakstype list |
	SLTFilter of string |
	SLTCheck of string |
	SLTSymEncFail of NewName.idtype
;;

let rec string_of_studyleakstype = function
	| SLTAnd ll -> if ll = [] then "TRUE" else "AND[" ^ (String.concat ", " (List.map string_of_studyleakstype ll)) ^ "]"
	| SLTOr ll -> if ll = [] then "FALSE" else "OR{" ^ (String.concat ", " (List.map string_of_studyleakstype ll)) ^ "}"
	| SLTFilter s -> "Filter(" ^ s ^ ")"
	| SLTCheck s -> "Check(" ^ s ^ ")"
	| SLTSymEncFail id -> "FailSymEnc(" ^ (NewName.to_string id) ^ ")"
;;

module SLTSet = MySet(struct type t = studyleakstype let compare = Pervasives.compare end);;


type studyleaksinputs =
	SLINormal of string
;;

module SLIMap = MyMap(struct type t = studyleaksinputs let compare = Pervasives.compare end);;

type studyleaksoutputs =
	SLONormal of string |
	SLOTraffic |
	SLOSymEncKey of NewName.idtype
;;

module SLOMap = MyMap(struct type t = studyleaksoutputs let compare = Pervasives.compare end);;

let writeFlowChecksFromSLT dg desc oc =
	output_string oc "{\n  \"inputs\": [";
	let isFirst = ref true
	in
	SLIMap.iter (fun inpElem _ ->
		(if not !isFirst then output_string oc ",");
		isFirst := false;
		output_string oc "\n    \"";
		output_string oc (match inpElem with SLINormal x -> x);
		output_string oc "\""
	) desc;
	let transpDesc = SLIMap.fold (fun inpElem inpDesc res ->
		SLOMap.fold (fun outpElem ioresults res' ->
			let resInps = try SLOMap.find outpElem res' with Not_found -> SLIMap.empty
			in
			let resInps' = SLIMap.add inpElem ioresults resInps
			in
			SLOMap.add outpElem resInps' res'
		) inpDesc res
	) desc SLOMap.empty
	in
	output_string oc "\n  ],\n  \"outputs\": [";
	let isFirstOutput = ref true
	in
	let outputSLT slt =
		let rec outputSLT' parens slt =
		match slt with
			| SLTFilter s -> output_string oc (s ^ " is passed")
			| SLTCheck s -> output_string oc (s ^ " holds")
			| SLTSymEncFail eid -> output_string oc ("Encryption no. " ^ (NewName.to_string eid) ^ " fails")
			| SLTAnd ll
			| SLTOr ll ->
				let isAnd = (match slt with SLTAnd _ -> true | _ -> false)
				in
				if List.length ll = 0 then
				begin
					output_string oc (if isAnd then "always" else "never")
				end
				else
				begin
					let needParens = parens && (List.length ll > 1)
					in
					(if needParens then output_string oc "(");
					let isNotFirst = ref false
					in
					List.iter (fun subslt ->
						(if !isNotFirst then
						begin
							output_string oc (if isAnd then " AND " else " OR ")
						end);
						outputSLT' true subslt;
						isNotFirst := true;
					) ll;
					(if needParens then output_string oc ")")
				end
		in
		if slt = SLTAnd [] then output_string oc "\"always\": null"
		else if slt = SLTOr [] then output_string oc "\"never\": null"
		else
		begin
			output_string oc "\"if\": \"";
			outputSLT' false slt;
			output_string oc "\""
		end
	in
	SLOMap.iter (fun outpElem resInps ->
		(if not !isFirstOutput then output_string oc ",");
		isFirstOutput := false;
		output_string oc "\n    {\n      \"";
		output_string oc (match outpElem with SLONormal s -> s | SLOTraffic -> "PUBLIC NETWORK MESSAGES" | SLOSymEncKey id -> "Use of encryption key at encryption no. " ^ (NewName.to_string id));
		output_string oc "\": [";
		let isFirstInput = ref true
		in
		SLIMap.iter (fun inpElem slt ->
			(if not !isFirstInput then output_string oc ",");
			isFirstInput := false;
			output_string oc "\n        {";
			outputSLT slt;
(*
			output_string oc ", \"input element\": \"";
			output_string oc (match inpElem with SLINormal s -> s);
			output_string oc "\"";
*)
			output_string oc "}"
		) resInps;
		output_string oc "\n      ]\n    }"
	) transpDesc;
	output_string oc "\n  ]\n}\n"
;;

let pathFromToFilter dg inpNodes describeFilter =
	let string_of_sltsetlist ss =
		"OR{" ^ (String.concat ", " (List.map (fun slts -> "AND[" ^ (String.concat ", " (List.map string_of_studyleakstype (SLTSet.elements slts))) ^ "]") ss)) ^ "}"
	in
	let initials = IdtSet.fold (fun nid -> IdtMap.add nid [SLTSet.empty]) inpNodes IdtMap.empty
	in
	let doNotPassFlow n prt =
		let d = n.nkind.nodelabel
		in
		if ((String.length d) >= 3) && ((safestringsub d 0 3) = "is_") then true else
		match prt with
		| PortOperInput opinpnum -> (
			let ll = match n.nkind.nodeintlbl with
		(*	| NNOperation OPEncrypt -> [1;2]
			| NNOperation OPDecrypt -> [1;2]
			| NNOperation (OPABEncrypt _) -> [1;2]
			| NNOperation OPABDecrypt -> [1;2] *)
			| _ -> []
		in
		List.mem opinpnum ll
		)
		| _ -> false
	in
	let finals = GrbOptimize.TopolSorter.fold (fun nid currFormulas ->
		let n = DG.findnode nid dg
		in
		let allIncomings = DG.nodefoldedges (fun ((IxM cc, eid),_,prt) ll -> (* do special flow cases here *)
			if doNotPassFlow n prt then ll else
			let Some (srcid,_,_) = cc.(0)
			in
			let srcll = try IdtMap.find srcid currFormulas with Not_found -> []
			in
			srcll @ ll
		) n (try IdtMap.find nid currFormulas with Not_found -> [])
		in
		let allIns1 = match (describeFilter n) with
			| None -> allIncomings
			| Some slt -> List.map (SLTSet.add slt) allIncomings
		in
		let allIns2 = List.sort_uniq Pervasives.compare allIns1
		in
		let allIns3 = List.filter (fun oneSet ->
			List.for_all (fun otherSet -> not ((oneSet <> otherSet) && (SLTSet.subset otherSet oneSet))) allIns2
		) allIns2
		in
		print_endline ("Node no. " ^ (NewName.to_string nid) ^ ", allIns2 = " ^ (string_of_sltsetlist allIns2) ^ ", allIns3 = " ^ (string_of_sltsetlist allIns3));
		IdtMap.add nid allIns3 currFormulas
	) dg initials
	in
	IdtMap.map (fun ss -> SLTOr (List.map (fun sss -> SLTAnd (SLTSet.elements sss)) ss)) finals
;;

let answersToSLI dg answers =
	let desc = ref SLIMap.empty
	in
	IdtMap.iter (fun inpNodeId _ ->
		let inpNode = DG.findnode inpNodeId dg
		in
		let inpName = inpNode.nkind.nodelabel
		in
		desc := SLIMap.add (SLINormal (safestringsub inpName 6 ((String.length inpName) - 6))) SLOMap.empty !desc
	) answers;
	let transpAnswers = IdtMap.fold (fun inpNodeId inpAnswers res ->
		RLMap.fold (fun outpName ioresults res' ->
			let resInps = try RLMap.find outpName res' with Not_found -> IdtMap.empty
			in
			let resInps' = IdtMap.add inpNodeId ioresults resInps
			in
			RLMap.add outpName resInps' res'
		) inpAnswers res
	) answers RLMap.empty
	in
	RLMap.iter (fun outpName resInps ->
		let outpElem =
			if (safestringsub outpName 0 7) = "Copy_of" then SLOTraffic
			else if (safestringsub outpName 0 6) = "Key of" then
				let preflen = String.length "Key of encryption "
				in
				SLOSymEncKey (NewName.from_string (safestringsub outpName preflen ((String.length outpName) - preflen)))
			else SLONormal outpName
		in
		IdtMap.iter (fun inpNodeId (withAll, withNone, allResults) ->
			let inpNode = DG.findnode inpNodeId dg
			in
			let inpName = inpNode.nkind.nodelabel
			in
			let inpElem = SLINormal (safestringsub inpName 6 ((String.length inpName) - 6))
			in
			let currFormula = try SLOMap.find outpElem (SLIMap.find inpElem !desc) with Not_found -> SLTOr []
			in
			let nextFormula =
			if withNone then SLTOr [] else
			if (not withAll) then SLTAnd [] else
			begin
				SLTOr (List.map (fun (badFuns, badChecks) ->
					SLTAnd (IdtSet.fold (fun filterNodeId ll ->
						let filterNode = DG.findnode filterNodeId dg
						in
						let filterElem = if (match filterNode.nkind.nodeintlbl with NNOperation OPEncrypt | NNOperation (OPABEncrypt _) -> true | _ -> false) then SLTSymEncFail filterNode.id else SLTFilter (filterNode.nkind.nodelabel)
						in
						filterElem :: ll
					) badFuns
					(IdtSet.fold (fun checkNodeId ll ->
						let checkNode = DG.findnode checkNodeId dg
						in
						let checkname = checkNode.nkind.nodelabel
						in
						(SLTCheck checkname) :: ll
					) badChecks []) )
				) allResults)
			end
			in
			desc := SLIMap.add inpElem (SLOMap.add outpElem (SLTOr [currFormula; nextFormula]) (SLIMap.find inpElem !desc)) !desc
		) resInps;
	) transpAnswers;
	!desc
;;

let analyseEncryptionFailures dg beforeFailureAnalysis =
	let rec markThingsHappening c pred ss =
		match ss with
		| SLTFilter _ | SLTCheck _ | SLTSymEncFail _ -> if pred ss then c else ss
		| SLTAnd ll -> SLTAnd (List.map (markThingsHappening c pred) ll)
		| SLTOr ll -> SLTOr (List.map (markThingsHappening c pred) ll)
	in
	let markThingsFailing = markThingsHappening (SLTAnd [])
	in
	let sslEnterLevel = ref (-1)
	in
	let sslTab () = 
		let rec wf n = if n <= 0 then "" else "    " ^ (wf (n-1))
		in
		wf !sslEnterLevel
	in
	let rec simplifyStudyLeaks ss = 
		sslEnterLevel := !sslEnterLevel + 1;
		print_endline ((sslTab ()) ^ "start simplifyStudyLeaks: " ^ (string_of_studyleakstype ss));
		let res =
		begin
		match ss with
		| SLTSymEncFail _
		| SLTCheck _
		| SLTFilter _ -> ss
		| SLTAnd ll
		| SLTOr ll ->
			let isAnd = (match ss with SLTAnd _ -> true | SLTOr _ -> false)
			in
			let llnew = List.map simplifyStudyLeaks ll
			in
			let rec flatten xx = match xx with
				| [] -> []
				| x :: xs -> (match x,isAnd with
					| SLTAnd y, true
					| SLTOr y, false -> y @ (flatten xs)
					| SLTAnd [y], _
					| SLTOr [y], _ -> y :: (flatten xs)
					| _ -> x :: (flatten xs)
				)
			in
			print_endline ((sslTab ()) ^ "Going to flatten the list " ^ (String.concat " | " (List.map string_of_studyleakstype llnew)));
			let llnew2 = flatten llnew
			in
			print_endline ((sslTab ()) ^ "This resulted in the list " ^ (String.concat " | " (List.map string_of_studyleakstype llnew2)));
			if isAnd && (List.mem (SLTOr []) llnew2) then SLTOr []
			else if (not isAnd) && (List.mem (SLTAnd []) llnew2) then SLTAnd []
			else
			let llnew3 = List.sort_uniq Pervasives.compare llnew2
			in
			if (llnew3 <> []) && (List.tl llnew3 = []) then List.hd llnew3 else
			if isAnd then SLTAnd llnew3 else SLTOr llnew3
		end
		in
		print_endline ((sslTab ()) ^ "result is " ^ (string_of_studyleakstype res));
		sslEnterLevel := !sslEnterLevel - 1;
		res
	in
	let rec checkImplication ssLeft ssRight =
		sslEnterLevel := !sslEnterLevel + 1;
		print_endline ((sslTab ()) ^ "Calling checkImplication with " ^ (string_of_studyleakstype ssLeft) ^ " and " ^ (string_of_studyleakstype ssRight));
		let rec (collectAtoms :  studyleakstype -> SLTSet.t list) = fun ss -> match ss with
			| SLTFilter _
			| SLTCheck _
			| SLTSymEncFail _ -> [SLTSet.singleton ss]
			| SLTAnd ll ->
				 let (resl : SLTSet.t list list) = List.map collectAtoms ll
				 in
				 List.map (List.fold_left SLTSet.union SLTSet.empty) (makeProducts (List.map Array.of_list resl))
			| SLTOr ll -> List.concat (List.map collectAtoms ll)
		in
		let res = List.for_all (fun atomset ->
			print_endline ((sslTab ()) ^ "Considering the set of atoms {" ^ (String.concat ", " (List.map string_of_studyleakstype (SLTSet.elements atomset))) ^ "}" );
			simplifyStudyLeaks (markThingsFailing (fun atom -> SLTSet.mem atom atomset) ssRight) <> SLTAnd []
		) (collectAtoms ssLeft)
		in
		print_endline ((sslTab ()) ^ "The result is " ^ (string_of_bool res));
		sslEnterLevel := !sslEnterLevel - 1;
		res
	in	
	let desc = ref beforeFailureAnalysis
	in
	
	print_endline "This is before simplification";
	SLIMap.iter (fun inpElem slomap ->
		print_endline ("Input object: " ^ (match inpElem with SLINormal s -> s));
		SLOMap.iter (fun outpElem v ->
			print_endline ("Output object: " ^ (match outpElem with SLONormal s -> s | SLOTraffic -> "NETWORK TRAFFIC" | SLOSymEncKey id -> ("Encryption key for " ^ (NewName.to_string id))) ^ ", V = " ^ (string_of_studyleakstype v) );
		) slomap
	) !desc;
	print_newline ();
	
	SLIMap.iter (fun inpElem slomap ->
		let m = ref slomap
		in
		SLOMap.iter (fun outpElem v ->
			m := SLOMap.add outpElem (simplifyStudyLeaks v) !m
		) slomap;
		desc := SLIMap.add inpElem !m !desc
	) !desc;
	
	print_endline "This is after simplification";
	SLIMap.iter (fun inpElem slomap ->
		print_endline ("Input object: " ^ (match inpElem with SLINormal s -> s));
		SLOMap.iter (fun outpElem v ->
			print_endline ("Output object: " ^ (match outpElem with SLONormal s -> s | SLOTraffic -> "NETWORK TRAFFIC" | SLOSymEncKey id -> ("Encryption key for " ^ (NewName.to_string id))) ^ ", V = " ^ (string_of_studyleakstype v) );
		) slomap
	) !desc;
	print_newline ();
	let oc = open_out "flowcheckbeforeenc"
	in
	writeFlowChecksFromSLT dg !desc oc;
	close_out oc;
	
	let foundFailingEncryptions = ref IdtSet.empty
	and makeFailEncIter = ref true
	in
	while !makeFailEncIter do
		let failingEncryptions = SLIMap.fold (fun inpElem slomap currset ->
			SLOMap.fold (fun outpElem sskey currset2 ->
				match outpElem with
					| SLOSymEncKey encid ->
					begin
						if sskey = SLTOr [] then currset2 else
						let sstraf = try SLOMap.find SLOTraffic slomap with Not_found -> SLTOr []
						in
						if checkImplication sskey sstraf then currset2 else IdtSet.add encid currset2
					end
					| _ -> currset2
			) slomap currset
		) !desc IdtSet.empty
		in
		let markEncsFailing = markThingsFailing (function SLTFilter _ | SLTCheck _ -> false | SLTSymEncFail x -> IdtSet.mem x failingEncryptions)
		in
		desc := SLIMap.fold (fun inpName slomap curr ->
			SLIMap.add inpName (
				SLOMap.fold (fun outpName v curr2 ->
					SLOMap.add outpName (simplifyStudyLeaks (markEncsFailing v)) curr2
				) slomap SLOMap.empty
			) curr
		) !desc SLIMap.empty;
		let newFoundFailingEncryptions = IdtSet.union !foundFailingEncryptions failingEncryptions
		in
		if IdtSet.is_empty (IdtSet.diff newFoundFailingEncryptions !foundFailingEncryptions) then
		begin
			makeFailEncIter := false
		end else
		begin
			makeFailEncIter := true;
			foundFailingEncryptions := newFoundFailingEncryptions
		end
	done;
	desc := SLIMap.map (fun slomap ->
		SLOMap.map (fun v ->
			simplifyStudyLeaks (markThingsHappening (SLTOr []) (function SLTSymEncFail _ -> true | _ -> false) v)
		) slomap
	) !desc;
	!desc
;;

let processChecks dg =
	let (checkNodes, checkNodeNames) = DG.foldnodes (fun n (ss, rs) ->
		let d = n.nkind.nodelabel
		in
		if (n.nkind.outputtype = VBoolean) && ((String.length d) >= 3) && ((safestringsub d 0 3) = "is_") then ((IdtMap.add n.id d ss), (RLMap.add d (IdtSet.add n.id (try RLMap.find d rs with Not_found -> IdtSet.empty)) rs)) else (ss,rs)
	) dg (IdtMap.empty, RLMap.empty)
	in
	let namesAsList = RLMap.fold (fun k _ ll -> k :: ll ) checkNodeNames []
	in
	(namesAsList, List.map (fun selChecks ->
		if selChecks = [] then ([], dg)
		else
		let dg0 = List.fold_right (fun selCheckName ->
			IdtSet.fold (fun nid dgcurr ->
				let nold = DG.findnode nid dg
				in
				let nnew = {nold with nkind = nkFalse; inputs = PortMap.empty; inputindextype = nold.outputindextype; ixtypemap = identityIndexMap () nold.outputindextype}
				in
				DG.changenode nnew dgcurr
			) (RLMap.find selCheckName checkNodeNames)
		) selChecks dg
		in
		let dg1 = GrbOptimize.removeDead ( (* fst *) (GrbOptimize.simplifyArithmetic dg0))
		in
		let oc = open_out ("finalgraph_" ^ (String.concat "_" selChecks) ^ ".dot")
		in
		GrbPrintWithCFlow.printgraph oc dg1;
		close_out oc;
		(selChecks, dg1)
	) (subsetlist namesAsList))
;;

let checkFlows dg =
	let allInputNodes = DG.foldnodes (fun n ss ->
		match n.nkind.nodeintlbl with
			| NNInput _ ->
				let inpName = n.nkind.nodelabel
				in
				if ((String.length inpName) >= 9) && ((safestringsub inpName 0 9) = "Input IV_") then ss else IdtSet.add n.id ss
			| _ -> ss
	) dg IdtSet.empty
	and allOutputNodes = DG.foldnodes (fun n ss ->
		match n.nkind.nodeintlbl with
			| NNOutput _ -> IdtSet.add n.id ss
			| _ -> ss
	) dg IdtSet.empty
	in
	let determineFilter n =
		if n.nkind.nodeintlbl = NNOperation OPEncrypt then Some (SLTSymEncFail n.id) else
		if (match n.nkind.nodeintlbl with NNOperation (OPABEncrypt _ ) -> true | _ -> false) then Some (SLTSymEncFail n.id) else
		let d = n.nkind.nodelabel
		in
		if ((String.length d) >= 7) && ((safestringsub d 0 7) = "filter_") then Some (SLTFilter d) else 
		if ((String.length d) >= 4) && ((safestringsub d 0 4) = "hash") then Some (SLTFilter d) else None
	in
	let (allChecks, checkResults) = processChecks dg
	in
	let allChecksAsSet = RLSet.of_list allChecks
	in
	let flowsForRemovedChecks = List.map (fun (removedChecks, simplerDg) ->
		print_endline ("Flowcheck, with the following set to false: " ^ (String.concat ", " removedChecks));
		let additionalSLTs = List.map (fun s -> SLTCheck s) (RLSet.elements (List.fold_right RLSet.remove removedChecks allChecksAsSet))
		in
		let flowsForInpNodes = IdtSet.fold (fun inpnodeid mm ->
			print_endline ("Starting Flowcheck for input node " ^ (NewName.to_string inpnodeid));
			let inpToOutp1 = pathFromToFilter simplerDg (IdtSet.singleton inpnodeid) determineFilter
			in
			let inpToOutp2 = IdtMap.filter (fun nid _ -> IdtSet.mem nid allOutputNodes) inpToOutp1
			in
			(* from output nodes to SLO-s *)
			let inpToOutp4 = IdtMap.fold (fun outpId v sltm ->
				let outpNames =
					let n = DG.findnode outpId dg
					in
					match n.nkind.nodeintlbl with NNOutput c -> c | _ -> RLSet.empty
				in
				let sltmnew = RLSet.fold (fun outpName sltmcurr ->
					let sloElem =
						if (safestringsub outpName 0 7) = "Copy_of" then SLOTraffic
						else if (safestringsub outpName 0 6) = "Key of" then
							let preflen = String.length "Key of encryption "
							in
							SLOSymEncKey (NewName.from_string (safestringsub outpName preflen ((String.length outpName) - preflen)))
							else SLONormal outpName
					in
					let sloV = try SLOMap.find sloElem sltmcurr with Not_found -> SLTOr []
					in
					let newV = match v,sloV with (SLTOr l1), (SLTOr l2) -> SLTOr (l1 @ l2)
					in
					SLOMap.add sloElem newV sltmcurr
				) outpNames sltm
				in
				sltmnew
			) inpToOutp2 SLOMap.empty
			in
			IdtMap.add inpnodeid inpToOutp4	mm
		) allInputNodes IdtMap.empty
		in
		(* from input nodes to SLIs *)
		let flowsForSlis = IdtMap.fold (fun inpNodeId slomap slim ->
			let inpNode = DG.findnode inpNodeId dg
			in
			let inpName = inpNode.nkind.nodelabel
			in
			SLIMap.add (SLINormal (safestringsub inpName 6 ((String.length inpName) - 6))) slomap slim
		) flowsForInpNodes SLIMap.empty
		in
		(additionalSLTs, flowsForSlis)
	) checkResults
	in
	flowsForRemovedChecks
;;
	
(*	
	let flowsForInpNodes = IdtSet.fold (fun inpnodeid mm ->
		print_endline ("Starting Flowcheck for input node " ^ (NewName.to_string inpnodeid));
		let flowForAnInpNodeAsList = List.map (fun (removedChecks, simplerDg) ->
			print_endline ("Flowcheck, with the following set to false: " ^ (String.concat ", " removedChecks));
			let inpToOutp1 = pathFromToFilter simplerDg (IdtSet.singleton inpnodeid) determineFilter
			in
			let inpToOutp2 = IdtMap.filter (fun nid _ -> IdtSet.mem nid allOutputNodes) inpToOutp1
			in
			let additionalSLTs = List.map (fun s -> SLTCheck s) (RLSet.elements (List.fold_right RLSet.remove removedChecks allChecksAsSet))
			in
			let inpToOutp3 = IdtMap.map (fun (SLTOr osltConjs) ->
				let nOsltConjs = List.map (fun (SLTAnd ll) -> SLTAnd (additionalSLTs @ ll)) osltConjs
				in
				SLTOr nOsltConjs
			) inpToOutp2
			in
			(* from output nodes to SLO-s *)
			let inpToOutp4 = IdtMap.fold (fun outpId v sltm ->
				let outpNames =
					let n = DG.findnode outpId dg
					in
					match n.nkind.nodeintlbl with NNOutput c -> c | _ -> RLSet.empty
				in
				let sltmnew = RLSet.fold (fun outpName sltmcurr ->
					let sloElem =
						if (safestringsub outpName 0 7) = "Copy_of" then SLOTraffic
						else if (safestringsub outpName 0 6) = "Key of" then
							let preflen = String.length "Key of encryption "
							in
							SLOSymEncKey (NewName.from_string (safestringsub outpName preflen ((String.length outpName) - preflen)))
							else SLONormal outpName
					in
					let sloV = try SLOMap.find sloElem sltmcurr with Not_found -> SLTOr []
					in
					let newV = match v,sloV with (SLTOr l1), (SLTOr l2) -> SLTOr (l1 @ l2)
					in
					SLOMap.add sloElem newV sltmcurr
				) outpNames sltm
				in
				sltmnew
			) inpToOutp3 SLOMap.empty
			in
			inpToOutp4
		) checkResults
		in
		let flowForAnInpNode = List.fold_right (SLOMap.merge (fun _ vl vr -> match vl,vr with
			| None, None -> None
			| Some x, None -> Some x
			| None, Some x -> Some x
			| Some (SLTOr l1), Some (SLTOr l2) -> Some (SLTOr (l1 @ l2))
		)) flowForAnInpNodeAsList SLOMap.empty
		in
		IdtMap.add inpnodeid flowForAnInpNode mm
	) allInputNodes IdtMap.empty
	in
	(* from input nodes to SLIs *)
	let flowsForSlis = IdtMap.fold (fun inpNodeId slomap slim ->
		let inpNode = DG.findnode inpNodeId dg
		in
		let inpName = inpNode.nkind.nodelabel
		in
		SLIMap.add (SLINormal (safestringsub inpName 6 ((String.length inpName) - 6))) slomap slim
	) flowsForInpNodes SLIMap.empty
	in
	flowsForSlis
;;
*)

let addAdditionalSLTs analResultList =
	let string_of_sltsetlist ss =
		"OR{" ^ (String.concat ", " (List.map (fun slts -> "AND[" ^ (String.concat ", " (List.map string_of_studyleakstype (SLTSet.elements slts))) ^ "]") ss)) ^ "}"
	in
	let rec simplifyOrAnds slt =
		let surroundAtoms f ll = List.map (fun s -> match s with SLTOr _ | SLTAnd _ -> s | _ -> f s) ll
		in
		let surroundAtomsOr = surroundAtoms (fun s -> SLTOr [s])
		and surroundAtomsAnd = surroundAtoms (fun s -> SLTAnd [s])
		in
		let rec simplifySingleton s = match s with SLTOr [ss] | SLTAnd [ss] -> simplifySingleton ss | _ -> s
		in
		let rec flattenORs = function
		| [] -> []
		| (x :: xs) -> (match x with SLTOr l -> flattenORs (l @ xs) | _ -> x :: (flattenORs xs))
		in
		let rec flattenANDs = function
		| [] -> []
		| (x :: xs) -> (match x with SLTAnd l -> flattenANDs (l @ xs) | _ -> x :: (flattenANDs xs))
		in
		let slt' = simplifySingleton slt
		in
		match slt' with
		| SLTOr ll ->
			let llnew = flattenORs (List.map simplifyOrAnds ll)
			in
			let llnew2 = List.map (fun (SLTAnd l) -> SLTSet.of_list l) (surroundAtomsAnd llnew)
			in
			let llnew3 = List.filter (fun oneSet ->
				List.for_all (fun otherSet -> not ((oneSet <> otherSet) && (SLTSet.subset otherSet oneSet))) llnew2
			) llnew2
			in
			print_endline ("llnew2 = " ^ (string_of_sltsetlist llnew2) ^ ", llnew3 = " ^ (string_of_sltsetlist llnew3));
			simplifySingleton (SLTOr (List.map (fun s -> simplifySingleton (SLTAnd (SLTSet.elements s))) llnew3))
		| SLTAnd ll ->
			let llnew = flattenANDs (List.map simplifyOrAnds ll)
			in
			let llnew2 = List.map (fun (SLTOr l) -> SLTSet.of_list l) (surroundAtomsOr llnew)
			in
			let llnew3 = List.filter (fun oneSet ->
				List.for_all (fun otherSet -> not ((oneSet <> otherSet) && (SLTSet.subset otherSet oneSet))) llnew2
			) llnew2
			in
			print_endline ("llnew2 = " ^ (string_of_sltsetlist llnew2) ^ ", llnew3 = " ^ (string_of_sltsetlist llnew3));
			simplifySingleton (SLTAnd (List.map (fun s -> simplifySingleton (SLTOr (SLTSet.elements s))) llnew3))
		| _ -> slt'
	in
	let interm = List.fold_right (fun (additionalSLTs, analResult) collResult ->
		let addResult = if additionalSLTs = [] then analResult else SLIMap.map (fun slomap ->
			SLOMap.map (fun cond -> match cond with
				| SLTOr osltConjs ->
					let nOsltConjs = List.map (fun cond' -> match cond' with SLTAnd ll -> SLTAnd (additionalSLTs @ ll) | _ -> SLTAnd (cond' :: additionalSLTs)) osltConjs
					in
					SLTOr nOsltConjs
				| SLTAnd xx -> SLTAnd (additionalSLTs @ xx)
				| _ -> SLTAnd (cond :: additionalSLTs)
			) slomap
		) analResult
		in
		SLIMap.merge (fun _ vl vr -> match vl,vr with
			| None, None -> None
			| Some x, None -> Some x
			| None, Some x -> Some x
			| Some addslomap, Some currslomap -> Some (SLOMap.merge (fun _ vl vr -> match vl,vr with
				| None, None -> None
				| Some x, None -> Some x
				| None, Some x -> Some x
				| Some x, Some y -> Some (match x,y with
					| SLTOr l1, SLTOr l2 -> SLTOr (l1 @ l2)
					| SLTAnd [], _ -> SLTAnd []
					| _, SLTAnd [] -> SLTAnd []
					| SLTOr l1, _ -> SLTOr (y :: l1)
					| _, SLTOr l2 -> SLTOr (x :: l2)
					| _, _ -> SLTOr [x;y]
				)
			) addslomap currslomap)
		) addResult collResult
	) analResultList SLIMap.empty
	in
	SLIMap.map (SLOMap.map simplifyOrAnds) interm
;;

