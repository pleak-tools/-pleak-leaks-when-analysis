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

let leaksAsGraphs dg resultdir =
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
			GrbPrint.printgraph oc dg'';
			close_out oc;
			ignore (graphToTree dg'' n resultdir)
		end
		else ()
	) dg ();;

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

let analysis dg =
	if (Array.length Sys.argv) < 2 then
	begin
		print_string ("Usage: " ^ Sys.executable_name ^ " folder_for_result_files\n");
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
	ignore (GrbOptimize.areIndicesInOrder "start" dg);
	let numnodes = DG.foldnodes (fun _ x -> x+1) dg 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "algusgraaf.dot"
	in
	GrbPrint.printgraph oc dg;
	close_out oc;
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
	let dgtmp = GrbOptimize.foldAndsTogether dgsplitted
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
	let dgsimpl1 = GrbOptimize.removeDead (GrbOptimize.foldIdentity (GrbOptimize.simplifyArithmetic dgjoinedNodes))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl1 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified1.dot"
	in
	GrbPrint.printgraph oc dgsimpl1;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl1" dgsimpl1);
	let dgsimpl2 = GrbOptimize.removeDead (GrbOptimize.foldAndsTogether (GrbOptimize.iseqToDimEq dgsimpl1))
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
	let dgsimpl4 = GrbOptimize.removeDead (GrbOptimize.moveAllOverEqualDims dgsimpl3a)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl4 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "simplified4.dot"
	in
	GrbPrint.printgraph oc dgsimpl4;
	close_out oc;
	ignore (GrbOptimize.areIndicesInOrder "simpl4" dgsimpl4);
	let dgstraightened = GrbOptimize.removeDead ( GrbOptimize.putTogetherNodes (GrbOptimize.removeDead (GrbOptimize.reduceAllNodeDim (GrbOptimize.foldAndsTogether (GrbOptimize.simplifyArithmetic (GrbOptimize.foldIdentity dgsimpl4))))))
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
	let dgsimpl4 = GrbOptimize.removeDead (GrbOptimize.moveAllOverEqualDims dgsimpl3)
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgsimpl4 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "r2simplified4.dot"
	in
	GrbPrint.printgraph oc dgsimpl4;
	close_out oc;
	let dgstraightened = GrbOptimize.removeDead (GrbOptimize.putTogetherNodes (GrbOptimize.removeDead (GrbOptimize.reduceAllNodeDim (GrbOptimize.foldAndsTogether (GrbOptimize.simplifyArithmetic (GrbOptimize.foldIdentity dgsimpl4))))))
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgstraightened 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "pre_finalgraph.dot"
	in
	GrbPrint.printgraph oc dgstraightened;
	close_out oc;
	let dgSingleOutputs = GrbOptimize.singleOutputPerValue dgstraightened
	in
	let numnodes = DG.foldnodes (fun _ x -> x+1) dgSingleOutputs 0
	in
	print_string "Number of nodes: "; print_int numnodes; print_newline ();
	let oc = open_out "finalgraph.dot"
	in
	GrbPrint.printgraph oc dgSingleOutputs;
	close_out oc;
(*	let oc = open_out "leakswhen.result"
	in
	GrbCollectLeaks.describeAllDependencies oc dgstraightened;
	close_out oc; *)
	leaksAsGraphs dgSingleOutputs resultfolder;
	makeLegend dgSingleOutputs resultfolder
;;

