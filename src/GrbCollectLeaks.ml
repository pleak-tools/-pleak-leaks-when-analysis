open GrbGraphs;;
open GrbCommons;;

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
		| NNInput _ -> [n.nkind.nodelabel n.ixtypemap, "always"]
		| NNOperation OPGeoDist
		| NNOperation OPPow
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
		| NNTakeDim _ -> n.nkind.nodelabel n.ixtypemap
		| NNTrue _ -> "TRUE"
		| NNFalse _ -> "FALSE"
		| NNError -> "ERROR"
		| NNInputExists _ -> n.nkind.nodelabel n.ixtypemap
		| NNInput _ -> "The value of " ^ (n.nkind.nodelabel n.ixtypemap)
		| NNOperation OPGeoDist ->
			let desc = collectInputDescs ()
			in
			"The geographic distance between the point with latitude {" ^ (PortMap.find (PortOperInput 1) desc) ^ "} and longitude {" ^ (PortMap.find (PortOperInput 2) desc) ^ "}, and the point with latitude {" ^ (PortMap.find (PortOperInput 3) desc) ^ "} and longitude {" ^ (PortMap.find (PortOperInput 4) desc) ^ "}"
		| NNOperation OPPow ->
			let desc = collectInputDescs ()
			in
			"The value {" ^ (PortMap.find (PortOperInput 1) desc) ^ "} raised to the power {" ^ (PortMap.find (PortOperInput 2) desc) ^ "}"
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
		if ((String.length tblname) >= 7) && ((String.uppercase (String.sub tblname 0 7)) = "UNKNOWN") then false else
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
	and nidredtbl = Hashtbl.create 10
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
			| EWRExists _ -> (Hashtbl.add nidprivtbl nid false; Hashtbl.add nidredtbl nid false)
			| EWRCompute (_, ll)
			| EWRComputeGen (_, ll) ->
				let upl = List.map doOutputEWR ll
				in
				let uplpriv = List.map (Hashtbl.find nidprivtbl) upl
				in
				let nidispriv =
					let res = List.fold_right (||) uplpriv false
					in
					Hashtbl.add nidprivtbl nid res; Hashtbl.add nidredtbl nid false; res
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
					| OPPow -> "^", false
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
					output_string oc ((dotnodeid nid) ^ " [shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=orange" else "filled") ^ " label=\"" ^ nodelbl ^ "\" fillcolor=white];\n");
					List.iteri (fun ifx upid ->
						output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid nid));
						let upidpriv = Hashtbl.find nidprivtbl upid
						in
						if (numberinps || upidpriv) then
						begin
							output_string oc " [";
							(if numberinps then output_string oc ("label=" ^ (string_of_int (ifx+1)) ^ " "));
							(if upidpriv then output_string oc "style=bold color=orange");
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
					Hashtbl.add nidredtbl nid false;
					output_string oc ((dotnodeid gbid) ^ " [shape=box style=" ^ (if gbidispriv then "\"filled,bold\" color=orange" else "filled") ^ " label=\"GROUP BY\" fillcolor=white];\n");
					output_string oc ((dotnodeid nid) ^ " [shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=orange" else "filled") ^ " label=\"" ^ nodelbl ^ "\" fillcolor=white];\n");
					output_string oc ((dotnodeid gbid) ^ " -> " ^ (dotnodeid nid) ^ (if gbidispriv then "[style=bold color=orange]" else "") ^ ";\n");
					output_string oc ((dotnodeid insideid) ^ " -> " ^ (dotnodeid nid) ^ (if Hashtbl.find nidprivtbl insideid then " [style=bold color=orange]" else "") ^ ";\n");
					List.iter (fun upid ->
						output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid gbid) ^ (if Hashtbl.find nidprivtbl upid then " [style=bold color=orange]" else "") ^ ";\n")
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
					Hashtbl.add nidredtbl nid false;
					output_string oc ((dotnodeid keyid) ^ " [shape=box style=" ^ (if keyispriv then "\"filled,bold\" color=orange" else "filled") ^ " label=\"KEY\" fillcolor=white];\n");
					output_string oc ((dotnodeid nid) ^ " [shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=orange" else "filled") ^ " label=\"SeqNo\" fillcolor=white];\n");
					output_string oc ((dotnodeid keyid) ^ " -> " ^ (dotnodeid nid) ^ (if keyispriv then " [style=bold color=orange]" else "") ^ ";\n");
					output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid nid) ^ (if upispriv then " [style=bold color=orange]" else "") ^ ";\n");
					List.iteri (fun idx gid ->
						output_string oc ((dotnodeid gid) ^ " -> " ^ (dotnodeid keyid) ^ " [label=" ^ (string_of_int (idx+1)) ^ (if Hashtbl.find nidprivtbl gid then " style=bold color=orange" else "") ^ "];\n")
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
			Hashtbl.add nidredtbl nid false;
			output_string oc ((dotnodeid nid) ^ "[shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=orange" else "filled") ^ " label=\"" ^ (match aot with AOTAnd _ -> "AND" | _ -> "OR") ^ "\" fillcolor=white];\n");
			List.iter (fun upid ->
				output_string oc ((dotnodeid upid) ^ " -> " ^ (dotnodeid nid) ^ (if Hashtbl.find nidprivtbl upid then " [style=bold color=orange]" else "") ^ ";\n");
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
			output_string oc ("subgraph cluster_" ^ (NewName.to_string thrid) ^ " {\n style=filled;\nfillcolor=turquoise\n\n")
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
		Hashtbl.add nidredtbl nid false;
		output_string oc ((dotnodeid nid) ^ "[shape=box style=" ^ (if nidispriv then "\"filled,bold\" color=" ^ (if (Hashtbl.find nidredtbl resid) || (Hashtbl.find nidredtbl condid) then "red" else "orange") else "filled") ^ " label=\"Filter\" fillcolor=" ^ (if atBeginning then "skyblue" else "white") ^ "];\n");
		output_string oc ((dotnodeid resid) ^ " -> " ^ (dotnodeid nid) ^ " [label=1" ^ (if resispriv then " style=bold color=" ^ (if Hashtbl.find nidredtbl resid then "red" else "orange") else "") ^ "];\n");
		output_string oc ((dotnodeid condid) ^ " -> " ^ (dotnodeid nid) ^ " [label=2" ^ (if condispriv then " style=bold color=" ^ (if Hashtbl.find nidredtbl condid then "red" else "orange") else "") ^ "];\n");
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
			output_string oc ((subgrstart oid) ^ " {\n  style=filled;\n  label=\"" ^ tbln ^ "\";\n  fillcolor=" ^ (if isFinalOut then "red" else if isExists then "khaki" else "green") ^";\n");
				RLSet.iter (fun attrname ->
					let (nid,_) = getEWRId (EWRInput (attrname, rid))
					in
					let nidispriv = isAttrPrivate tbln attrname
					in
					Hashtbl.add nidprivtbl nid nidispriv;
					Hashtbl.add nidredtbl nid nidispriv;
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
			output_string oc ("subgraph cluster_" ^ (NewName.to_string thrid) ^ " {\n style=filled;\nfillcolor=turquoise\n\n")
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
		output_string oc ((dotnodeid nid) ^ "[shape=box label=\"Filter\" fillcolor=" ^ (if atBeginning then "skyblue style=filled" else "white style=filled") ^ "];\n");
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
			output_string oc ((subgrstart oid) ^ " {\n  style=filled;\n  label=\"" ^ tbln ^ "\";\n  fillcolor=" ^ (if isFinalOut then "red" else if isExists then "khaki" else "green") ^";\n");
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

