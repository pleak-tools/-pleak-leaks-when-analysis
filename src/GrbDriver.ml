open GrbGraphs;;

let () =
	let (dg, _, _) = GrbInput.convertRA RAInput.aiddistrDbdesc RAInput.aiddistrQuery
(*	let (dg, _, _) = GrbInput.convertRA RAInput.dbdesc RAInput.query *)
	in
	GrbAnalyzer.analysis dg
;;

