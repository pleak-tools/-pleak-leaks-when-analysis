open GrbGraphs;;
open GrbCommons;;

type mappingDirection = MDForward | MDBackward;;

let hexstring_of_int n =
	let hexdigits = [| "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "A"; "B"; "C"; "D"; "E"; "F" |]
	in
	let nhigh = n / 16
	in
	let nlow = n - nhigh * 16
	in
	hexdigits.(nhigh) ^ hexdigits.(nlow)
;;

let printgraph oc dg gdns = (* Sends the description of dg in the dot format to the channel oc *)
	let needsValuetype =
		DG.foldnodes (fun n b ->
			if b then true else
			let checkIndexType (AITT a) =
				let res = ref false
				in
				Array.iter (Array.iter (fun (vt,_) -> if vt <> VInteger then res := true)) a;
				!res
			in (checkIndexType n.inputindextype) || (checkIndexType n.outputindextype)
		) dg false
	in
	let dotnodeid x = "v_" ^ (NewName.to_string x)
	and dotedgeid x = "e_" ^ (NewName.to_string x)
	and outputMasked s =
		String.iter (function
			| '<' -> output_string oc "\\<"
			| '>' -> output_string oc "\\>"
			| c -> output_char oc c
		) s
	in
	let outputMapInVContext a b m mapdir =
		let outputSeqInVContext nums dims =
			Array.iteri (fun idx n ->
				(if idx > 0 then output_string oc "| " else ());
				let (vt,tp) = dims.(idx)
				in
				output_string oc ("{ " ^ (string_of_int n) ^ (if needsValuetype then " | " ^ (string_of_valuetype vt) else "") ^ " | ");
				(match tp with
					| None -> ()
					| Some s -> outputMasked (s ^ " ")
				);
				output_string oc "} "
			) nums
		in
		let aa = a.(0)
		and bb = b.(0)
		and mm = let Some (_,_,x) = m.(0) in x
		in
		let aseq,bseq = match mapdir with
			| MDForward -> Array.of_list (intfromto 0 ((Array.length aa) - 1)), mm
			| MDBackward -> mm, Array.of_list (intfromto 0 ((Array.length bb) - 1))
		in
		if (aa = bb) && (aseq = bseq) then
		begin
			outputSeqInVContext aseq aa
		end else
		begin
		output_string oc "{ { ";
		outputSeqInVContext aseq aa;
		output_string oc "} ";
		(match mapdir with
			| MDForward -> output_string oc " | -\\> | "
			| MDBackward -> output_string oc " | \\<- | " );
		output_string oc "{ ";
		outputSeqInVContext bseq bb;
		output_string oc "} } "
		end
	in
	let outputMapInVContextWithGDims nodeid a b m =
		let outputSeqInVContext strOfNum nums dims =
			let needsValueName =
				Array.fold_right (fun (_,tp) bb ->
					if bb then true
					else (match tp with None -> false | Some _ -> true)
				) dims false
			in
			Array.iteri (fun idx n ->
				(if idx > 0 then output_string oc "| " else ());
				let (vt,tp) = dims.(idx)
				in
				output_string oc ("{ " ^ (strOfNum n) ^ (if needsValuetype then " | " ^ (string_of_valuetype vt) else ""));
				(if needsValueName then begin
					output_string oc " | ";
					match tp with
						| None -> output_string oc "_ "
						| Some s -> outputMasked (s ^ " ")
					
				end);
				output_string oc "} "
			) nums
		in
		let aa = a.(0)
		and bb = b.(0)
		and mm = let Some (_,_,x) = m.(0) in x
		in
		let aseq,bseq = Array.of_list (intfromto 0 ((Array.length aa) - 1)), mm
		in
		if (aa = bb) && (aseq = bseq) then
		begin
			output_string oc "{ { ";
			(try
				let gdseq = Array.of_list (List.map snd (IntMap.bindings (IdtMap.find nodeid gdns)))
				in
				let gdtypes = Array.map (fun _ -> (VInteger, None)) gdseq
				in
				outputSeqInVContext NewName.to_string gdseq gdtypes
			with Not_found -> ());
			output_string oc " } | { ";
			outputSeqInVContext string_of_int aseq aa;
			output_string oc "} } "
		end else
		begin
			output_string oc "{ { ";
			(try
				let gdseq = Array.of_list (List.map snd (IntMap.bindings (IdtMap.find nodeid gdns)))
				in
				let gdtypes = Array.map (fun _ -> (VInteger, None)) gdseq
				in
				outputSeqInVContext NewName.to_string gdseq gdtypes
			with Not_found -> ());
			output_string oc " } | { ";
			outputSeqInVContext string_of_int aseq aa;
			output_string oc "} ";
			output_string oc " | -\\> | ";
			output_string oc "{ ";
			outputSeqInVContext string_of_int bseq bb;
			output_string oc "} } "
		end
	in
	output_string oc "digraph {\n";
	DG.foldnodes (fun nn () ->
		let (AITT a) = nn.inputindextype
		and (AITT b) = nn.outputindextype
		and (IxM m) = nn.ixtypemap
		and (bgr,bgg,bgb) = nn.nkind.nodecolor
		and (fgr,fgg,fgb) = nn.nkind.nodetextcolor
		in
		let colorattrs = "style=filled fillcolor=\"#" ^ (hexstring_of_int bgr) ^ (hexstring_of_int bgg) ^ (hexstring_of_int bgb) ^ "\" fontcolor=\"#" ^ (hexstring_of_int fgr) ^ (hexstring_of_int fgg) ^ (hexstring_of_int fgb) ^ "\""
		in
		if (Array.length a = 1) && (Array.length b = 1) then
		begin
			output_string oc ((dotnodeid nn.id) ^ "[shape=record " ^ colorattrs ^ " label=\"{ ");
			output_string oc "{ ";
			outputMasked (nn.nkind.nodelabel);
			output_string oc (" | " ^ (NewName.to_string nn.id) ^ " } | ");
			outputMapInVContext a b m MDForward;
			output_string oc " }\"];\n"
		end else
		begin
			output_string oc ((dotnodeid nn.id) ^ " [" ^ colorattrs ^ " label=\"");
			output_string oc ((nn.nkind.nodelabel) ^ " " ^ (NewName.to_string nn.id) ^ "\"];\n")
		end
	) dg ();
	DG.foldedges (fun ((cc,eid),nn,prt) () ->
		let (IxM m) = cc
		in
		let isNonIdentity (Some (_,_,backmap)) =
			let res = ref false
			in
			Array.iteri (fun idx n -> if idx <> n then res := true) backmap;
			!res
		in
		if (Array.length m = 1) && (match m.(0) with None -> false | Some _ -> true) && (isNonIdentity m.(0)) then
		begin
			let (AITT b) = nn.inputindextype
			in
			let Some (srcid,_,_) = m.(0)
			in
			let srcn = DG.findnode srcid dg
			in
			let (AITT a) = srcn.outputindextype
			in
			output_string oc ((dotedgeid eid) ^ "[shape=Mrecord label=\"{ " ^ (portdesc prt).wirename ^ " | ");
			outputMapInVContext a b m MDBackward;
			output_string oc " }\"];\n"
		end else
		begin
			output_string oc ((dotedgeid eid) ^ " [shape=plaintext label=\"" ^ (portdesc prt).wirename ^ "\" width=0 height=0];\n")
		end;
		DG.foldedgesources (fun srcid () ->
			output_string oc ( (dotnodeid srcid) ^ ":s -> " ^ (dotedgeid eid) ^ ":n [dir=none];\n" )
		) (cc,eid) ();
		output_string oc ( (dotedgeid eid) ^ ":s -> " ^ (dotnodeid nn.id) ^ ":n;\n" )
	) dg ();
	output_string oc "}\n";;

