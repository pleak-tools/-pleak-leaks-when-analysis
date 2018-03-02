open GrbGraphs;;

let leaksAsGraphs dg =
	DG.foldnodes (fun n () ->
		if n.nkind.nodeintlbl = NNOutput then
		begin
			let dg' = DG.foldnodes (fun n' dgcurr ->
				if (n'.nkind.nodeintlbl = NNOutput) && (n.id <> n'.id) then
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
			close_out oc
		end
		else ()
	) dg ();;

let analysis dg =
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
	let oc = open_out "r2straightened.dot"
	in
	GrbPrint.printgraph oc dgstraightened;
	close_out oc;
	let oc = open_out "leakswhen.result"
	in
	GrbCollectLeaks.describeAllDependencies oc dgstraightened;
	close_out oc;
	leaksAsGraphs dgstraightened
;;

