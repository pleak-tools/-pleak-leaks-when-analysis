open GrbGraphs;;

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
		| NNTrue
		| NNFalse
		| NNError -> []
		| NNInputExists _
		| NNInput _ -> [n.nkind.nodelabel n.ixtypemap, "always"]
		| NNOperation OPGeoDist
		| NNOperation OPDiv
		| NNNot
		| NNAnd
		| NNLongOr
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
		| NNMakeBag _
		| NNAggregate AGMakeBag
		| NNFilter _
		| NNOutput ->
			let inputdescPl = ref None
			and controldescPl = ref ""
			in
			DG.nodefoldedges (fun ((IxM m,eid),_,prt) () ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in
				match prt with
					| PortSingleB ->
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
					| PortSingleB ->
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
		| NNAnd ->
			let inpdescs = DG.nodefoldedges (fun ((IxM m,eid),_,prt) ll ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in (describeCondition dg ninp) :: ll
			) n []
			in "All of the following hold: [" ^ (String.concat ", " inpdescs) ^ "]"
		| NNOr ->
			let inpdescs = DG.nodefoldedges (fun ((IxM m,eid),_,prt) ll ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in (describeCondition dg ninp) :: ll
			) n []
			in "At least one of the following holds: [" ^ (String.concat ", " inpdescs) ^ "]"
		| NNNot ->
				let inpdescs = DG.nodefoldedges (fun ((IxM m,eid),_,prt) ll ->
				let Some (srcid,_,_) = m.(0)
				in
				let ninp = DG.findnode srcid dg
				in (describeCondition dg ninp) :: ll
			) n []
			in "The statement \"" ^ (List.hd inpdescs) ^ "\" does not hold"
		| NNTakeDim _ -> n.nkind.nodelabel n.ixtypemap
		| NNTrue -> "TRUE"
		| NNFalse -> "FALSE"
		| NNError -> "ERROR"
		| NNInputExists _ -> n.nkind.nodelabel n.ixtypemap
		| NNInput _ -> "The value of " ^ (n.nkind.nodelabel n.ixtypemap)
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
		| NNMakeBag _
		| NNAggregate AGMakeBag ->
			let descs = collectInputDescs ()
			and VBag (dims,vt) = n.nkind.outputtype
			in
			"A collection of {" ^ (PortMap.find (PortSingle vt) descs) ^ "} grouped along " ^ (String.concat ", " (List.map fst dims)) (* ^ ", for rows satisfying " ^ (PortMap.find PortSingleB descs) *)
		| NNFilter vt ->
			let descs = collectInputDescs ()
			in
			"The value of {" ^ (PortMap.find (PortSingle vt) descs) ^ "}, only if " ^ (PortMap.find PortSingleB descs) ^ " holds true"
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
		| NNLongOr ->
			let desc = collectInputDescs ()
			in
			"One of the many {" ^ (PortMap.find PortSingleB desc) ^ "} holds"
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
			"If " ^ (PortMap.find PortSingleB desc) ^ " then " ^ (PortMap.find (PortTrue vt) desc) ^ " else " ^ (PortMap.find (PortFalse vt) desc)
		| NNOutput -> ""
;;

let describeAllDependencies oc dg =
	DG.foldnodes (fun n () ->
		match n.nkind.nodeintlbl with
			| NNOutput ->
				let deps = describeDependency dg n
				in
				output_string oc ("Output no. " ^ (NewName.to_string n.id));
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

