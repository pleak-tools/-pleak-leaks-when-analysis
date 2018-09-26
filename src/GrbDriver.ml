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
(*	let (dg, _, _) = GrbInput.convertRA RAInput.onlySlotsDbdesc RAInput.onlySlotsQuery *)
(*	let (dg, _, _) = GrbInput.convertRA RAInput.aiddistrDbdesc RAInput.aiddistrQuery *)
(*	let (dg, _, _) = GrbInput.convertRA RAInput.dbdesc RAInput.query *)
(*	let dg = BpmnInput.convertBPMN Chronosync.wholeproc Chronosync.useddatasets Chronosync.inpdatasets *)
	let (wholeproc, useddatasets, inpdatasets) = PleakBpmn.convertXMLBPMN "example.bpmn"
	in
	let dg = BpmnInput.convertBPMN wholeproc useddatasets inpdatasets
	in
	GrbAnalyzer.analysis dg
;;

