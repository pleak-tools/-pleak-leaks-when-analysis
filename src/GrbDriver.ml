open GrbGraphs;;

let rec printoutxml colltags indent thing = 
	let printspaces n =
		for i = 1 to n do
			print_char ' '
		done
	in
	match thing with
	| Xml.Element (tagname, attrs, children) ->
	begin
		colltags := RLSet.add tagname !colltags;
		printspaces indent;
		print_string "ELEMENT: "; print_string tagname; print_newline ();
		List.iter (fun (attrname, attrval) ->
			printspaces indent; print_string "ATTR: "; print_string attrname; print_string " IS "; print_string attrval; print_newline ()
		) attrs;
		printspaces indent; print_string "CONTENT:\n";
		List.iter (fun childthing ->
			printoutxml colltags (indent + 4) childthing
		) children;
		printspaces indent; print_string "END OF ELEMENT "; print_string tagname; print_newline ()
	end
	| Xml.PCData s -> (printspaces indent; print_string "PCDATA: "; print_string s; print_newline ())
;;

let () =
	let (resultfolder, possBpmnFile) = GrbAnalyzer.readParameters ()
	in
	match possBpmnFile with
		| None ->
			let (dg, _, _) = GrbInput.convertRA RAInput.aiddistrDbdesc RAInput.aiddistrQuery
			in
			GrbAnalyzer.analysis dg true resultfolder
		| Some bpmnFile ->
			let (wholeproc, useddatasets, inpdatasets) = PleakBpmn.convertXMLBPMN bpmnFile
			in
			let dg = BpmnInput.convertBPMN wholeproc useddatasets inpdatasets
			in
			GrbAnalyzer.analysis dg false resultfolder
;;

