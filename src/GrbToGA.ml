(* This module rewrites queries to a form that would be compatible with hssqlppp parser and hence 'guessing advantage' and 'constraint propagation' analyses *)
(* Similarly to leaks-when, it uses the content of RAInput.ml as an input *)
open GrbInput;;
open GrbGraphs;;

exception Err of string

let addPrefix x y = if (x = "") then y else x ^ "." ^ y
let alias (x,y) = String.concat " AS "  [x;y]
let error e      = raise (Err ("ERROR: " ^ e))
let failure e    = begin
		       print_string e;
		       exit 1
	           end;;

let queryString tableName (sel, fr, wh, gr, ord) = "INSERT INTO " ^ tableName ^ " SELECT " ^ (String.concat ", " (List.map alias sel)) ^ " FROM " ^ (String.concat ", " (List.map alias fr)) ^ (if List.length wh > 0 then " WHERE " else "") ^ (String.concat ", " wh) ^ (if List.length gr > 0 then " GROUP BY " else "") ^ (String.concat ", " gr) ^ (if List.length ord > 0 then " ORDER BY " else "")  ^ (String.concat ", " ord) ^ ";"

let rec toAggr = function
    | AGMax -> "MAX"
    | AGMin -> "MIN"
    | AGSum -> "SUM"
    | AGCount -> "COUNT"
    | AGAverage -> "AVG"
    | AGExist -> error "aggregation EXIST is not supported yet"
    | AGMakeBag -> error "aggregation BAG is not supported yet"
;;


let rec toAexpr = 
let toFun = function
| (OPPlus, xs) -> "(" ^ (String.concat " + " (List.map toAexpr xs)) ^ ")"
| (OPNeg, [x]) -> "(-(" ^  toAexpr x ^ "))"
| (OPMult, xs) -> "(" ^ (String.concat " * " (List.map toAexpr xs)) ^ ")"
| (OPIsEq, [x;y]) ->  "(" ^ toAexpr x ^ " = " ^ toAexpr y ^ ")"
| (OPLessThan, [x;y]) ->  "(" ^ toAexpr x ^ " < " ^ toAexpr y ^ ")"
| (OPLessEqual, [x;y]) ->  "(" ^ toAexpr x ^ " <= " ^ toAexpr y ^ ")"
| (OPGreaterThan, [x;y])  ->  "(" ^ toAexpr x ^ " > " ^ toAexpr y ^ ")"
| (OPGreaterEqual, [x;y]) -> "(" ^ toAexpr x ^ " >= " ^ toAexpr y ^ ")"
| (OPAnd, xs) -> "(" ^ (String.concat " AND " (List.map toAexpr xs)) ^ ")"
| (OPOr,  xs) -> "(" ^ (String.concat " OR  " (List.map toAexpr xs)) ^ ")"
| (OPNot, [x]) -> "(NOT(" ^ toAexpr x ^ "))"
| (OPDiv, [x;y]) -> "(" ^ toAexpr x ^ " / " ^ toAexpr y ^ ")"
| (OPPow, [x;y]) -> "(" ^ toAexpr x ^ " ^ " ^ toAexpr y ^ ")"
| (OPGeoDist, [x1;x2;y1;y2]) -> "(POINT(" ^ toAexpr x1 ^ "," ^ toAexpr x2 ^ ") <@> POINT(" ^ toAexpr y1 ^ "," ^ toAexpr y2 ^ "))"
| (OPCoalesce, [x]) -> "(COALESCE(" ^ toAexpr x ^ "))"
| (OPCeiling, [x]) -> "(CEIL(" ^ toAexpr x ^ "))"
| (OPIntConst x, _) -> string_of_int x
| (OPStringConst s, _) -> "\'" ^ s ^ "\'"
| (OPRealConst r, _) -> string_of_float r
| (OPBoolConst b, _) -> string_of_bool b
| (OPNull vt, _) -> "NULL"
| (OPITE, [RAXoper (OPLessThan, [x1;y1]);x2;y2]) ->
       if (x1 = x2) && (y1 = y2) then
           "(LEAST(" ^ toAexpr x1 ^ "," ^ toAexpr y1 ^ "))"
       else if (x1 = y2) && (y1 = x2) then
           "(GREATEST(" ^ toAexpr x1 ^ "," ^ toAexpr y1 ^ "))"
       else
           "(CASE WHEN " ^ toAexpr (RAXoper (OPLessThan, [x1;y1])) ^ " THEN " ^ toAexpr x2 ^ " ELSE " ^ toAexpr y2 ^ " END)"
| (OPITE, [b;x;y]) -> "(CASE WHEN " ^ toAexpr b ^ " THEN " ^ toAexpr x ^ " ELSE " ^ toAexpr y ^ " END)"
| (OPTuple _, xs) -> "(" ^ (String.concat ", " (List.map toAexpr xs)) ^ ")"
| (OPProject s, _) -> error "projections inside arithetic expressions are not supported yet"
| (OPOrder b, _) -> error "orderings inside arithetic expressions are not supported yet"
| (op, zs) -> error (Printf.sprintf ("Cannot interpret arithmetic operation %s with %d arguments.") (string_of_opname op) (List.length zs))
in function
    | RAXattribute x -> x
    | RAXoper (f,xs) -> toFun (f, xs)
;;


(* the output is a triple (sel = [col,alias],from,where,groupby) *)
let rec toQexpr ot oc schema = function
    | RATable tblname -> let (colMap,_)   = (if RLMap.mem tblname schema then RLMap.find tblname schema else error (tblname ^ " not found in the schema")) in
                         let colNames     = List.map fst (RLMap.bindings colMap) in
                         (List.map (fun x -> (x,x)) colNames, [(tblname,tblname)], [], [], [])
    | RAFilter (subexp, filterexp) -> let (sel, fr, wh, gr, ord) = toQexpr ot oc schema subexp in
                                      let fstr = toAexpr filterexp in
                                      (sel, fr, List.append wh [fstr], gr, ord)
    | RAProject (subexp, keptcols) -> let (sel0, fr, wh, gr, ord) = toQexpr ot oc schema subexp in
                                      let sel = List.filter (fun (_,x) -> List.mem x keptcols) sel0 in
                                      (sel, fr, wh, gr, ord)
    | RANewColumn (subexp, colname, colexp) -> let (sel, fr, wh, gr, ord) = toQexpr ot oc schema subexp in
                                               let colvalue = toAexpr colexp in
                                               (List.append sel [(colvalue, colname)], fr, wh, gr, ord)

    (* assumption: we only rename pure columns of subexpr and do not go deeper *)
    | RARenameCol (oldcolname, newcolname, subexp) ->  let (sel0, fr0, wh, gr, ord) = toQexpr ot oc schema subexp in
                                                       let sel = List.map (fun (x,y) -> if (y = oldcolname) then
                                                                                            if String.contains oldcolname '.' then (y,newcolname)
                                                                                            else (x,newcolname)
                                                                                         else (x,y)) sel0 in
                                                       let prefix = List.hd (String.split_on_char '.' newcolname) in
                                                       let fr = if (prefix = newcolname) then fr0
                                                                else List.map (fun (tn,ta) -> if RLMap.mem oldcolname (fst (RLMap.find tn schema)) then (tn,prefix) else (tn,ta)) fr0 in
                                                       (sel, fr, wh, gr, ord)

    (* assumption: we can only aggregate by pure columns and not expressions *)
    | RAAggregate (subexp, groupattrs, aggroattrs) -> let (sel, fr, wh, gr0, ord) = toQexpr ot oc schema subexp in
                                                      let aggrColNames = List.map fst aggroattrs in
                                                      let sel0     = List.filter (fun (_,x) -> not (List.mem x aggrColNames)) sel in
                                                      let aggrVals = List.map fst (List.filter (fun (_,x) -> List.mem x aggrColNames) sel) in
                                                      let sel1     = List.map2 (fun (colname, aggr) colexpr -> (toAggr aggr ^ "(" ^ colexpr ^ ")", colname)) aggroattrs aggrVals in
                                                      let gr = groupattrs in
                                                      (List.append sel0 sel1, fr, wh, List.append gr0 gr, ord)

    | RALetExp (newtblname, newtblexp, restexp) -> let (sel0, fr0, wh0, gr0, ord0) = toQexpr ot oc schema newtblexp in

                                                   (* this is fine as far as we do not need types in the schemas *)
                                                   let newColMap = List.fold_right (fun (_,x) m -> RLMap.add x NoValue m) sel0 RLMap.empty in
                                                   let newKeys   = [] in
                                                   let newSchema = RLMap.add newtblname (newColMap, newKeys) schema in

                                                   output_string oc (queryString newtblname (sel0, fr0, wh0, gr0, ord0) ^ "\n\n");
                                                   if (not ("" = ot)) && (newtblname = ot) then ([],[],[],[],[]) else
                                                   let (sel1, fr1, wh1, gr1, ord1) = toQexpr ot oc newSchema restexp in
                                                   (sel1, fr1, wh1, gr1, ord1)

    | RACartesian subexps -> List.fold_right (fun s (sel0,fr0,wh0,gr0,ord0) -> let (sel,fr,wh,gr,ord) = toQexpr ot oc schema s in (List.append sel sel0 , List.append fr fr0 , List.append wh wh0, List.append gr gr0, List.append ord ord0)) subexps ([],[],[],[],[])

    | RAAddSortColumn (subexp, newcolname, contractcols, sortcol) -> let (sel0, fr0, wh0, gr0, ord0) = toQexpr ot oc schema subexp in
                                                                 let sel = List.filter (fun (_,x) -> not (List.mem x contractcols)) sel0 in
                                                                 (List.append sel [("row_number()", newcolname)], fr0, wh0, gr0, List.append ord0 [sortcol])

    | RAUnionWithDifferentSchema (_, _) -> ([],[],[],[],[])
    | RAUnion (_, _)                    -> ([],[],[],[],[])

    | RAIntersection (_, _)             -> error "Intersection of tables is not supported yet."
    | RADifference (_, _)               -> error "Difference of tables is not supported yet."
    | RANonmatchingJoin (_, _, _)       -> error "Non-matching JOIN of tables (LEFT, RIGHT) is not supported yet."

let () =
        let argc = Array.length Sys.argv in
	let schema = RAInput.aiddistrDbdesc in
        let query = RAInput.aiddistrQuery in
        let oc = if argc < 2 then failure ("Usage: " ^ Sys.executable_name ^ " folder_for_result_file [target_object]\n") else open_out Sys.argv.(1) in
        let ot = if argc < 3 then "" else Sys.argv.(2) in
        ignore (toQexpr ot oc schema query);
        close_out oc;
;

