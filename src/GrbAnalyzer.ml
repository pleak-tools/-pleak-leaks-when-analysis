open GrbGraphs;;

let graphToTree dg n resultdir =
	let changedg = ref DG.empty
	in
	let rec mkDeepCopy n =
		let newn = {n with
			id = NewName.get ();
			inputs = PortMap.empty
		}
		in
		changedg := DG.addnode newn !changedg;
		DG.nodefoldedges (fun ((IxM cc, eid), _, prt) () ->
			let Some (srcid, _, backmap) = cc.(0)
			in
			let src = DG.findnode srcid dg
			in
			let newsrcid = mkDeepCopy src
			in
			changedg := DG.addedge ((IxM [| Some (newsrcid, 0, backmap) |], NewName.get ()), newn.id, prt) !changedg
		) n ();
		newn.id
	in
	let newnid = mkDeepCopy n
	in
	let (ewd, gdns) = GrbCollectLeaks.dependencyOfAnOutput !changedg (DG.findnode newnid !changedg) None
	in
	let oc = open_out ("tree_of_" ^ (NewName.to_string n.id) ^ ".dot")
	in
	GrbPrint2.printgraph oc !changedg gdns;
	close_out oc;
	let trewd = GrbCollectLeaks.translateEWD ewd
	in
	let oc = open_out (resultdir ^ "/leakage_from_" ^ (NewName.to_string n.id) ^ ".dot")
	in
	GrbCollectLeaks.output_ewr_to_graph oc trewd;
	close_out oc;
	let oc = open_out (resultdir ^ "/leakage_from_" ^ (NewName.to_string n.id) ^ ".result")
	in
	GrbCollectLeaks.output_ewr oc trewd;
	close_out oc;
	(!changedg, newnid)
;;

let leaksAsGraphs dg resultdir isSQL =
	DG.foldnodes (fun n () ->
		if (match n.nkind.nodeintlbl with NNOutput _ -> true | _ -> false) then
		begin
			let dg' = DG.foldnodes (fun n' dgcurr ->
				if (match n'.nkind.nodeintlbl with NNOutput _ -> true | _ -> false) && (n.id <> n'.id) then
					DG.remnode n'.id dgcurr
				else
					dgcurr
			) dg dg
			in
			let dg'' = GrbOptimize.removeDead dg'
			in
			let oc = open_out ("deps_of_" ^ (NewName.to_string n.id) ^ ".dot")
			in
			GrbPrintWithCFlow.printgraph oc dg'';
			close_out oc;
			(if isSQL then ignore (graphToTree dg'' n resultdir) )
(*			let sccarr = GrbOptimize.SCCFinder.scc_array dg''
			in
			print_string "Found strongly connected components\n";
			Array.iter (fun nodelist ->
				if (List.length nodelist) > 1 then
				begin
					print_string "Found a component: ";
					print_string (String.concat ", " (List.map NewName.to_string nodelist));
					print_newline ()
				end
			) sccarr *)
		end
		else ()
	) dg ();;

let debugGraph dg =
	let dg' = DG.foldnodes (fun n' dgcurr ->
		if (match n'.nkind.nodeintlbl with NNOutput _ -> true | _ -> false) then
			DG.remnode n'.id dgcurr
		else
			dgcurr
	) dg dg
	in
	let n = DG.findnode (NewName.from_int 3481) dg'
	in
	let nn = {
		nkind = nkOutput VBoolean RLSet.empty;
		id = NewName.get ();
		inputindextype = n.outputindextype;
		outputindextype = n.outputindextype;
		ixtypemap = identityIndexMap () n.outputindextype;
		inputs = PortMap.empty;
	}
	in
	let dg2 = DG.addnode nn dg'
	in
	let dg3 = DG.addedge ((identityIndexMap n.id n.outputindextype, NewName.get ()), nn.id,PortSingleB) (DG.addedge ((identityIndexMap n.id n.outputindextype, NewName.get ()), nn.id,PortSingle VBoolean) dg2)
	in
	let dg4 = GrbOptimize.removeDead dg3
	in
	let oc = open_out "debug_v3481.dot"
	in
	GrbPrint.printgraph oc dg4;
	close_out oc
;;

let makeLegend dg resultdir =
	let rescoll = DG.foldnodes (fun n m ->
		match n.nkind.nodeintlbl with
			| NNOutput outp ->
				RLSet.fold (fun outstr mm ->
					let s = try RLMap.find outstr mm with Not_found -> IdtSet.empty
					in
					RLMap.add outstr (IdtSet.add n.id s) mm
				) outp m
			| _ -> m
	) dg RLMap.empty
	in
	let oc = open_out (resultdir ^ "/legend")
	in
	output_string oc "{\n";
	let finishPreviousLine = ref false
	in
	RLMap.iter (fun outpname resnodes ->
		let fnames = List.map (fun nid -> "\"leakage_from_" ^ (NewName.to_string nid) ^ ".dot\"") (IdtSet.elements resnodes)
		in
		if !finishPreviousLine then
		begin
			output_string oc ",\n"
		end;
		output_string oc "  \"";
		output_string oc outpname;
		output_string oc "\": [";
		output_string oc (String.concat ", " fnames);
		output_string oc "]";
		finishPreviousLine := true
	) rescoll;
	output_string oc "\n}\n";
	close_out oc
;;

let writeFlowChecks dg answers oc =
	output_string oc "{\n  \"inputs\": [";
	let isFirst = ref true
	in
	IdtMap.iter (fun inpNodeId _ ->
		(if not !isFirst then output_string oc ",");
		isFirst := false;
		let inpNode = DG.findnode inpNodeId dg
		in
		let inpName = inpNode.nkind.nodelabel inpNode.ixtypemap
		in
		output_string oc "\n    \"";
		output_string oc (String.sub inpName 6 ((String.length inpName) - 6));
		output_string oc "\""
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
	output_string oc "\n  ],\n  \"outputs\": [";
	let isFirstOutput = ref true
	in
	RLMap.iter (fun outpName resInps ->
		(if not !isFirstOutput then output_string oc ",");
		isFirstOutput := false;
		output_string oc "\n    {\n      \"";
		output_string oc outpName;
		output_string oc "\": [";
		let isFirstInput = ref true
		in
		IdtMap.iter (fun inpNodeId (withAll, withNone, allResults) ->
			(if not !isFirstInput then output_string oc ",");
			isFirstInput := false;
			output_string oc "\n        {";
			if withNone then output_string oc "\"never\": null}" else
			if (not withAll) then output_string oc "\"always\": null}" else
			begin
				let hasSeveralElements = ((List.length allResults) > 1)
				in
				output_string oc "\"if\": \"";
				let isNotFirst = ref false
				in
				List.iter (fun (badFuns, badChecks) ->
					(if !isNotFirst then output_string oc " OR ");
					isNotFirst := true;
					let needsBrackets = (((IdtSet.cardinal badFuns) + (IdtSet.cardinal badChecks)) > 1) && hasSeveralElements
					in
					(if needsBrackets then output_string oc "(");
					let isNotFstInGrp = ref false
					in
					IdtSet.iter (fun filterNodeId ->
						(if !isNotFstInGrp then output_string oc " AND ");
						isNotFstInGrp := true;
						let filterNode = DG.findnode filterNodeId dg
						in
						let filtername = filterNode.nkind.nodelabel filterNode.ixtypemap
						in
						output_string oc (filtername ^ " is passed")
					) badFuns;
					IdtSet.iter (fun checkNodeId ->
						(if !isNotFstInGrp then output_string oc " AND ");
						isNotFstInGrp := true;
						let checkNode = DG.findnode checkNodeId dg
						in
						let checkname = checkNode.nkind.nodelabel checkNode.ixtypemap
						in
						output_string oc (checkname ^ " holds")
					) badChecks;
					(if needsBrackets then output_string oc ")");
				) allResults;
				output_string oc "\"}"
			end
		) resInps;
		output_string oc "\n      ]\n    }"
	) transpAnswers;
	output_string oc "\n  ]\n}\n"
;;
	
(*	
	IdtMap.iter (fun inpNodeId inpAnswers ->
		let inpNode = DG.findnode inpNodeId dg
		in
		let inpName = inpNode.nkind.nodelabel inpNode.ixtypemap
		in
		RLMap.iter (fun outpName (withAll, withNone, withFilter, withCheck) ->
			output_string oc (String.sub inpName 6 ((String.length inpName) - 6));
			output_string oc "\t";
			output_string oc outpName;
			output_string oc "\t";
			if withNone then output_string oc "NEVER LEAKS" else
			if (not withAll) then output_string oc "ALWAYS LEAKS" else
			begin
				output_string oc "Leaks only if";
				let isNotFirst = ref false
				in
				IdtMap.iter (fun filterNodeId fb ->
					if fb then () else
					begin
						(if !isNotFirst then output_string oc " OR");
						isNotFirst := true;
						let filterNode = DG.findnode filterNodeId dg
						in
						let filtername = filterNode.nkind.nodelabel filterNode.ixtypemap
						in
						output_string oc (" " ^ filtername ^ " is passed")
					end
				) withFilter;
				IdtMap.iter (fun checkNodeId fb ->
					if fb then () else
					begin
						(if !isNotFirst then output_string oc " OR");
						isNotFirst := true;
						let checkNode = DG.findnode checkNodeId dg
						in
						let checkname = checkNode.nkind.nodelabel checkNode.ixtypemap
						in
						output_string oc (" " ^ checkname ^ " holds")
					end
				) withCheck
			end;
			output_string oc "\n"
		) inpAnswers
	) answers
;;
*)


let readParameters () =
	if (Array.length Sys.argv) < 2 then
	begin
		print_string ("Usage: " ^ Sys.executable_name ^ " folder_for_result_files [name_of_analysed_BP.bpmn]\n");
		exit 1
	end;
	let resultfolder = Sys.argv.(1)
	in
	(try
		if Sys.is_directory resultfolder then () else
		begin
			print_string (resultfolder ^ " is not a folder\n");
			exit 1
		end
	with Sys_error _ -> begin
			print_string (resultfolder ^ " does not exist\n");
			exit 1
		end
	);
	let bpmnFile = if (Array.length Sys.argv) = 2 then None else (Some Sys.argv.(2))
	in (resultfolder, bpmnFile)
;;

let analysis dg isSQL resultfolder =
	let numnodes = DG.foldnodes (fun _ x -> x+1) dg 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "algusgraaf.dot"
	in
	GrbPrint.printgraph oc dg;
	close_out oc;
	(*debugGraph dg;*)
			(let sccarr = GrbOptimize.SCCFinder.scc_array dg
			in
			print_string "Found strongly connected components\n";
			Array.iter (fun nodelist ->
				if (List.length nodelist) > 1 then
				begin
					print_string "Found a component: ";
					print_string (String.concat ", " (List.map NewName.to_string nodelist));
					print_newline ()
				end
			) sccarr);
	ignore (GrbOptimize.areIndicesInOrder "start" dg);
	let dgnodead = GrbOptimize.removeDead (GrbOptimize.areIndicesInOrder "blaah1" (GrbOptimize.foldIdentity dg))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgnodead 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "nodeads.dot"
	in
	GrbPrint.printgraph oc dgnodead;
	close_out oc;
	let dgsplitted = GrbOptimize.areIndicesInOrder "splitted" (GrbOptimize.splitIndexTypes dgnodead)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsplitted 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "splitted.dot"
	in
	GrbPrint.printgraph oc dgsplitted;
	close_out oc;
	let dgtmp = GrbOptimize.foldMaxsTogether (GrbOptimize.foldAndsTogether dgsplitted)
	in
	ignore (GrbOptimize.areIndicesInOrder "foldands" dgtmp);
	print_string "Now going to reduce dimensions\n";
	let dgNoAndAnds = GrbOptimize.areIndicesInOrder "reduceDim" (GrbOptimize.reduceAllNodeDim (GrbOptimize.removeDead dgtmp ))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgNoAndAnds 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "noandands.dot"
	in
	GrbPrint.printgraph oc dgNoAndAnds;
	close_out oc;
	let dgjoinedNodes = GrbOptimize.putTogetherNodes dgNoAndAnds
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgjoinedNodes 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "joinednodes.dot"
	in
	GrbPrint.printgraph oc dgjoinedNodes;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "joinedNodes" dgjoinedNodes);
	let dgsimpl0 = GrbOptimize.removeDead (GrbOptimize.unrollCycles dgjoinedNodes (GrbOptimize.proposeMultiplicity dgjoinedNodes))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl0 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified0.dot"
	in
	GrbPrint.printgraph oc dgsimpl0;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl0" dgsimpl0);
	let dgsimpl1 = GrbOptimize.removeDead (GrbOptimize.foldIdentity (GrbOptimize.simplifyArithmetic dgsimpl0))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl1 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified1.dot"
	in
	GrbPrint.printgraph oc dgsimpl1;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl1" dgsimpl1);
	let dgsimpl2 = GrbOptimize.removeDead (GrbOptimize.foldMaxsTogether (GrbOptimize.foldAndsTogether (GrbOptimize.iseqToDimEq dgsimpl1)))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl2 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified2.dot"
	in
	GrbPrint.printgraph oc dgsimpl2;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl2" dgsimpl2);
	let dgsimpl3 = GrbOptimize.removeDead (GrbOptimize.reduceAndDimension dgsimpl2)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl3 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified3.dot"
	in
	GrbPrint.printgraph oc dgsimpl3;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl3" dgsimpl3);
	let dgsimpl3a = GrbOptimize.removeDead (GrbOptimize.reduceLongorDimension dgsimpl3)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl3a 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified3a.dot"
	in
	GrbPrint.printgraph oc dgsimpl3a;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl3a" dgsimpl3a);
	let dgsimpl4 = GrbOptimize.removeDead (GrbImplication.removeRedundantEdgesWithZ3 dgsimpl3a)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl4 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified4.dot"
	in
	GrbPrint.printgraph oc dgsimpl4;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl4" dgsimpl4);
	let oc = open_out "descMax.z3"
	in
	GrbImplication.writeOrderingToZ3 dgsimpl4 oc;
	GrbImplication.askZ3ForRedundantMaxEdges dgsimpl4 oc;
	close_out oc;
	let dgsimpl4aa = GrbOptimize.removeDead (GrbImplication.removeRedundantMaxEdges dgsimpl4)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl4aa 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified4aa.dot"
	in
	GrbPrint.printgraph oc dgsimpl4aa;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl4aa" dgsimpl4);
	let dgsimpl4a = GrbOptimize.removeDead (GrbOptimize.moveAllOverEqualDims dgsimpl4aa)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl4a 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified4a.dot"
	in
	GrbPrint.printgraph oc dgsimpl4a;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl4a" dgsimpl4a);
	let dgstraightened =
		let prgr x g =
			let oc = open_out ("interm_" ^ (string_of_int x) ^ ".dot")
			in
			GrbPrint.printgraph oc g;
			close_out oc
		in
		let g1 = GrbOptimize.foldIdentity dgsimpl4a
		in
		prgr 1 g1;
		let g2 = GrbOptimize.simplifyArithmetic g1
		in
		prgr 2 g2;
		let g3 = GrbOptimize.foldAndsTogether g2
		in
		prgr 3 g3;
		let g4 = GrbOptimize.foldMaxsTogether g3
		in
		prgr 4 g4;
		let g5 = GrbOptimize.reduceAllNodeDim g4
		in
		prgr 5 g5;
		let g6 = GrbOptimize.removeDead g5
		in
		prgr 6 g6;
		let g7 = GrbImplication.removeRedundantEdgesWithZ3 g6
		in
		prgr 7 g7;
		let g8 = GrbOptimize.removeDead g7
		in
		prgr 8 g8;
		let g9 = GrbOptimize.putTogetherNodes g8
		in
		prgr 9 g9;
		let g10 = GrbOptimize.removeDead g9
		in
		g10
(*	let dgstraightened = GrbOptimize.removeDead ( GrbOptimize.putTogetherNodes (GrbOptimize.removeDead (GrbImplication.removeRedundantEdgesWithZ3 (GrbOptimize.removeDead (GrbOptimize.reduceAllNodeDim (GrbOptimize.foldMaxsTogether (GrbOptimize.foldAndsTogether (GrbOptimize.simplifyArithmetic (GrbOptimize.foldIdentity dgsimpl4a)))))))))  *)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgstraightened 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "straightened.dot"
	in
	GrbPrint.printgraph oc dgstraightened;
	close_out oc;
	let dgsimpl3 = GrbOptimize.removeDead (GrbOptimize.removeOutputControlDims dgstraightened)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl3 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "r2simplified3.dot"
	in
	GrbPrint.printgraph oc dgsimpl3;
	close_out oc;
	let dgsimpl4 = GrbOptimize.removeDead (GrbOptimize.moveAllOverEqualDims (GrbOptimize.removeDead (GrbImplication.removeRedundantEdgesWithZ3 dgsimpl3)))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl4 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "r2simplified4.dot"
	in
	GrbPrint.printgraph oc dgsimpl4;
	close_out oc;
	let dgsimpl5 = (* GrbOptimize.moveLongorsDown (GrbOptimize.removeDead (GrbOptimize.moveNotsUp (GrbOptimize.removeDead ( *) GrbOptimize.moveFilterDown (GrbOptimize.removeDead (GrbOptimize.moveJustMergeDown (GrbOptimize.removeDead (GrbOptimize.moveMergeDown dgsimpl4)))) (* )))) *)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl5 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "r2simplified5.dot"
	in
	GrbPrint.printgraph oc dgsimpl5;
	close_out oc; 
	let dgsimpl6 = GrbOptimize.dimFunDepsToDimEqs (GrbOptimize.removeDead dgsimpl5)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl6 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "r2simplified6.dot"
	in
	GrbPrint.printgraph oc dgsimpl6;
	close_out oc; 
	let dgsimpl6a = GrbOptimize.removeDead (GrbOptimize.moveAllOverEqualDims (GrbOptimize.removeDead (GrbOptimize.reduceLongorDimension (GrbOptimize.removeDead (GrbOptimize.reduceAndDimension (GrbOptimize.removeDead (GrbOptimize.foldAndsTogether dgsimpl6)))))))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl6a 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "r2simplified6a.dot"
	in
	GrbPrint.printgraph oc dgsimpl6a;
	close_out oc; 
	let dgstraightened = GrbOptimize.removeDead (GrbOptimize.simplifyArithmetic (GrbOptimize.singleOutputPerValue (GrbOptimize.removeDead (GrbOptimize.putTogetherNodes (GrbOptimize.removeDead (GrbOptimize.compareDiffFunDeps (GrbOptimize.removeDead (GrbOptimize.reduceAllNodeDim (GrbOptimize.foldMaxsTogether (GrbOptimize.foldAndsTogether (GrbOptimize.simplifyArithmetic (GrbOptimize.foldIdentity dgsimpl6a))))))))))))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgstraightened 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "pre_finalgraph.dot"
	in
	GrbPrint.printgraph oc dgstraightened;
	close_out oc;
	let dgAfterZ3 = GrbImplication.removeRedundantEdgesWithZ3 dgstraightened
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgAfterZ3 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "afterZ3.dot"
	in
	GrbPrint.printgraph oc dgAfterZ3;
	close_out oc;
	let dgSingleOutputs = (* GrbOptimize.removeDead (GrbImplication.removeRedundantEdgesWithZ3 ( *)  GrbOptimize.removeDead (GrbOptimize.foldIdentity (GrbOptimize.simplifyArithmetic (GrbOptimize.foldIdentity (GrbOptimize.simplifyArithmetic (GrbOptimize.removeDead dgAfterZ3))))) (* )) *)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgSingleOutputs 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "finalgraph.dot"
	in
	GrbPrintWithCFlow.printgraph oc dgSingleOutputs;
	close_out oc;
(*	let oc = open_out "leakswhen.result"
	in
	GrbCollectLeaks.describeAllDependencies oc dgstraightened;
	close_out oc; *)
	let oc = open_out "desc4.z3"
	in
	GrbImplication.writeBooleanDescToZ3 dgSingleOutputs oc;
	GrbImplication.askZ3ForRedundantEdges dgSingleOutputs oc;
	close_out oc;
			(let dataedges = GrbOptimize.findDataEdges dgSingleOutputs
			in
			let dg' = DG.foldedges (fun ((_,eid),_,_) dg' -> if not (IdtSet.mem eid dataedges) then DG.remedge eid dg' else dg') dgSingleOutputs dgSingleOutputs
			in
			let sccarr = GrbOptimize.SCCFinder.scc_array dg'
			in
			print_string "Found strongly connected components\n";
			Array.iter (fun nodelist ->
				if (List.length nodelist) > 1 then
				begin
					print_string "Found a component: ";
					print_string (String.concat ", " (List.map NewName.to_string nodelist));
					print_newline ()
				end
			) sccarr);
	leaksAsGraphs dgSingleOutputs resultfolder isSQL;
	(if isSQL then makeLegend dgSingleOutputs resultfolder);
	(if not isSQL then
	begin
		let oc = open_out "descAll.z3"
		in
		GrbImplication.writeItAllToZ3 dgSingleOutputs oc;
		close_out oc;
		ignore (GrbImplication.checkFlows dgSingleOutputs (Some "descAll.z3"));
		let aboutFlows = GrbImplication.checkFlows dgSingleOutputs None
		in
		let oc = open_out (resultfolder ^ "/flowcheckresults")
		in
		writeFlowChecks dgSingleOutputs aboutFlows oc;
		close_out oc
	end
	)
;;

