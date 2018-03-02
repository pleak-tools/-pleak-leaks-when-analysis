open GrbCommons;;
open GrbGraphs;;

(* names of attributes and names of tables are strings *)
(* raexpressiontype is the type of relational algebra expressions. A value of type raexpressiontype is the input to the leaks-when analysis. Another input to the analysis are the schemas of the tables *)
(* The result of executing a relational algebra expression is a dataset. The dataset has columns with certain names; these can be determined from the expression and the schemas of the tables *)

type raexpressiontype = RATable of string	(* The meaning of this should be clear *)
					  | RAFilter of raexpressiontype * raanyexp (* ... and this one as well *)
					  | RAProject of raexpressiontype * string list (* ... and this one as well. The second argument lists the column that are left in the result *)
					  | RACartesian of raexpressiontype list (* Cartesian product of several datasets. The names of columns in these datasets should all be different --- we do not have mechanisms to _automatically_ rename columns *)
					  | RAUnion of raexpressiontype * raexpressiontype (* Here both datasets should have the same schema *)
					  | RAUnionWithDifferentSchema of raexpressiontype * raexpressiontype (* Here the datasets should have disjoint sets of attributes. This operation adds more columns to both datasets, filling them with NULLs, such that they will have the same schema. Then it unions them. *)
					  | RAIntersection of raexpressiontype * raexpressiontype (* Here too *)
					  | RADifference of raexpressiontype * raexpressiontype (* And here too *)
					  | RANewColumn of raexpressiontype * string * raanyexp (* Here a new column is computed. For each row in the dataset, the value in the new column is computed from the values in existing columns (the same applies to the expression in RAFilter *)
					  | RAAggregate of raexpressiontype * (string list) * ((string * aggregationname) list) (* RAAggregate (ds, groupbylist, aggrlist) does the aggregation of the dataset ds, according to the values in the columns named in groupbylist. For each element (colname, aggr), we add the column colname to the result, the value of which is the aggregation aggr of the column colname in the dataset ds *)
					  | RALetExp of string * raexpressiontype * raexpressiontype (* RALetExp(tablename, tableexp, mainexp) first computes the dataset described by tableexp, and gives it the name tablename. The expression mainexp can access the result of tableexp by invoking "RATable tablename" *)
					  | RARenameCol of string * string * raexpressiontype (* RARenameCol(oldname, newname, ds) computes the dataset ds and then renames its column oldname to newname *)
					  | RANonmatchingJoin of raexpressiontype * raexpressiontype * raanyexp (* RANonMatchingJoin(ds1, ds2, exp) computes the difference of "ds1 LEFT JOIN ds2 ON exp" and "ds1 INNER JOIN ds2 ON exp"  *)
					  | RAAddSortColumn of raexpressiontype * string * (string list) * string (* The arguments are: original expression, the name of the order column, the columns to be contracted, the column to be sorted. It adds a new column (of type Integer) to the dataset, where the ordering number of the to-be-sorted column is given. In the pandemic scenario, this is achieved by first sorting the dataset and then adding to it the column row_number(). *)
and  raanyexp = RAXattribute of string | RAXoper of operationname * raanyexp list;; (* An expression is evaluated in the context of a dataset row. The expression is either an attribute value, or an operation applied to expressions. Future work: add tables of the database to the context, and allow them to be used in expressions (e.g. "EXISTS (SELECT ... FROM ... WHERE ...)") *)

type columndescriptiontype = valuetype;;

type tabledescriptiontype = (columndescriptiontype RLMap.t) * (RLSet.t list);; (* the second component is the indices. It must not be empty *)

type dbdescriptiontype = tabledescriptiontype RLMap.t;;

(* type attrlocationtype = (NewName.idtype * indexmaptype) annotindextypetype;; *)
(* type attrlocationtype = (bool annotindextypetype * NewName.idtype * indexmaptype) list;; *)
(* type attrlocationtype = NewName.idtype annotindexmaptype;; *) (* For each component of the attribute's indextype: (1) the ID of the node, (2) the component of the indextype of the node, (3) mapping between the components of the indextypes of the attribute and the node *)
(*type attrlocationtype = (NewName.idtype * int * int array) array;;*)
type attrlocationtype = NewName.idtype;;

(*
let attrlocProdtypeLeft (AITT t1) (AITT t2) al =
	let l1 = Array.length t1
	and l2 = Array.length l2
	in
	Array.init (l1*l2) (fun i ->
		let xl = i / l2
		and xr = i mod l2
		in
		let (nodeid, compid, backmap) = al.(xl)
		in
		(nodeid, compid, backmap)
	);;

let attrlocProdtypeRight (AITT t1) (AITT t2) al =
	let l1 = Array.length t1
	and l2 = Array.length l2
	in
	Array.init (l1*l2) (fun i ->
		let xl = i / l2
		and xr = i mod l2
		in
		let (nodeid, compid, backmap) = al.(xr)
		in
		(nodeid, compid, Array.map (fun y -> l1 + y) backmap)
	);;

let (combineattrlocations : DG.t -> (NewName.idtype * int * int array * int) list -> (NewName.idtype list * int * int array)) dg locs =
	let (nl, c, bm, _) = List.fold_right (fun (nodeid, onecompnum, onebackmap, typewidth) (currlist, currcomp, currbackmap, curraddends) ->
		let (AITT oit) = (DG.findnode nodeid dg).outputindextype
		in
		let numaddends = Array.length oit
		in
		let newbackmap = Array.append onebackmap (Array.map (fun x -> x + typewidth) currbackmap)
		and newaddends = numaddends * curraddends
		and newcompnum = onecompnum * curraddends + currcomp
		and newlist = nodeid :: currlist
		in (newlist, newcompnum, newbackmap, newaddends)
	) locs ([], 0, [||], 1)
	in (nl, c, bm);;
*)

type tablelocationtype = attrlocationtype * attrlocationtype RLMap.t * indextypetype;; (* First component --- existence node. Second component --- nodes for attributes. Third component --- the considered index type for a query *)

type dblocationtype = tablelocationtype RLMap.t;;

let (makeinputnodes : dbdescriptiontype -> DG.t * dblocationtype) = fun dbdesc ->
  let pickBestIdx ll = List.hd ll (* more logic should be included here *)
  in
  RLMap.fold (fun tblname (coldescs,tblindices) (dg, collocs) ->
  	let bestidx = pickBestIdx tblindices (* bestidx : RLSet.t *)
  	in
  	let tblindextype = AITT (Array.make 1 (Array.of_list (List.map (fun s -> (RLMap.find s coldescs, Some s)) (RLSet.elements bestidx))))
  	in
    let (dgfin', collocsonetable) = RLMap.fold (fun colname cval (dg', collocs') ->
      let newid = NewName.get ()
      in
      let nodelocation = newid
      in
      let newnode = if RLSet.mem colname bestidx then
      begin
      {
      	nkind = nkTakeDim colname cval;
      	id = newid;
      	inputs = PortMap.empty;
      	inputindextype = tblindextype;
      	outputindextype = tblindextype;
      	ixtypemap = identityIndexMap () tblindextype;
      }
      end
      else
      {
      	nkind = nkInput cval (tblname ^ "." ^ colname);
      	id = newid;
      	inputs = PortMap.empty;
      	inputindextype = tblindextype;
      	outputindextype = tblindextype;
      	ixtypemap = identityIndexMap () tblindextype;
      }
      in
      let dg'' = DG.addnode newnode dg'
      in
      (dg'', RLMap.add colname nodelocation collocs')
    ) coldescs (dg, RLMap.empty)
    in 
    let existencenodeid = NewName.get ()
    in
    let existencenode =
      {
        nkind = nkInputExists tblname;
        id = existencenodeid;
        inputs = PortMap.empty;
        inputindextype = tblindextype;
        outputindextype = tblindextype;
        ixtypemap = identityIndexMap () tblindextype;
      }
    in
    let dgfin = DG.addnode existencenode dgfin'
    in
    (dgfin, RLMap.add tblname (existencenodeid, collocsonetable, tblindextype) collocs)
  ) dbdesc (DG.empty, RLMap.empty);;  

module ComparableIdList =
struct
	type t = NewName.idtype list
	let compare = Pervasives.compare
end;;

module IdListMap = Map.Make(ComparableIdList);;

let (addNodesToGraph : DG.t -> indextypetype -> attrlocationtype list -> nodekind -> (int -> portname) -> DG.t * attrlocationtype) = fun dg' ixtype arglocs mynkind portfn ->
	let changedg = ref dg'
	and nodeedgetypes = ref IdtMap.empty
	and nodeinps = ref IdtMap.empty (* maps nodeid to a list of pairs (source node id, port of the edge) *)
	and nodeidmap = ref IdListMap.empty
	in
	
	let nnid = NewName.get ()
	in
	let nn = {
		nkind = mynkind;
		id = nnid;
		inputindextype = ixtype;
		outputindextype = ixtype;
		ixtypemap = identityIndexMap () ixtype;
		inputs = PortMap.empty;
	}
	in
	changedg := DG.addnode nn !changedg;
	List.iter2 (fun argnodeid portidx ->
		changedg := DG.addedge ((identityIndexMap argnodeid ixtype, NewName.get ()), nnid, portfn portidx) !changedg
	) arglocs (intfromto 0 ((List.length arglocs) - 1));
	(!changedg, nnid);;

(* let addNodesToGraph dg' ixtype arglocs mynkind portfn = addContractingNodesToGraph dg' ixtype (identityIndexMap () ixtype) ixtype arglocs mynkind portfn;; *)

(* let mkColumnsEqual fstcolname sndcolname dg attrlocs --- maybe not such a good idea... *)

let (putIdNodeOnTop : DG.t -> attrlocationtype -> indextypetype -> indextypetype -> indexmaptype -> DG.t * attrlocationtype) = fun dg nid origixtype newixtype projmap ->
	let nnid = NewName.get ()
	and nold = DG.findnode nid dg
	in
	let vtype = nold.nkind.outputtype
	in
	let nn = {
		nkind = nkId vtype;
		id = nnid;
		inputindextype = newixtype;
		outputindextype = newixtype;
		ixtypemap = identityIndexMap () newixtype;
		inputs = PortMap.empty;
	}
	in
	(DG.addedge ((mapindexmap (fun () -> nid) projmap, NewName.get ()) , nnid, PortSingle vtype) (DG.addnode nn dg), nnid);;

let (putIdNodeOnSum : DG.t -> (attrlocationtype * indextypetype) list -> indextypetype -> DG.t * attrlocationtype) = fun dg nidstypes newixtype ->
	let nnid = NewName.get ()
	and vtype = (DG.findnode (fst (List.hd nidstypes)) dg).nkind.outputtype
	in
	let nn = {
		nkind = nkId vtype;
		id = nnid;
		inputindextype = newixtype;
		outputindextype = newixtype;
		ixtypemap = identityIndexMap () newixtype;
		inputs = PortMap.empty;
	}
	in
	let connmap = List.fold_right (fun (oldid, oldixtype) (IxM tmpmap) -> 
		let (IxM newmap) = identityIndexMap oldid oldixtype
		in IxM (Array.append newmap tmpmap) ) nidstypes (IxM [||])
	in
	(DG.addedge ((connmap, NewName.get ()) , nnid, PortSingle vtype) (DG.addnode nn dg), nnid);;
	

let onlyAggregation dgtmp ((filterloc, attrlocs, ixtype) as tblloctmp) groupattrs aggroattrs =
	let aggroOutputType aggrop singvt =
		match aggrop with
			| AGMakeBag -> (
				match singvt with
					| VTuple [(_,VTuple dims);(_,vt)] -> VBag (dims,vt)
					| _ -> singvt
			)
			| _ -> singvt
	in
	let columndesc s =
		let n = DG.findnode (RLMap.find s attrlocs) dgtmp
		in n.nkind.outputtype
	in
  	let aggrindextype = AITT (Array.make 1 (Array.of_list (List.map (fun s -> (columndesc s, Some s)) groupattrs)))
  	in
  	let changedg = ref dgtmp
  	in
  	let grouplocs = List.fold_right (fun grname mm ->
  		let nnid = NewName.get ()
  		in
  		let nn = {
	      	nkind = nkTakeDim grname (columndesc grname);
	      	id = nnid;
	      	inputs = PortMap.empty;
	      	inputindextype = aggrindextype;
	      	outputindextype = aggrindextype;
	      	ixtypemap = identityIndexMap () aggrindextype;
		}
		in
		changedg := DG.addnode nn !changedg;
		RLMap.add grname nnid mm
  	) groupattrs RLMap.empty
  	in
	let (jointtype, [projmapaggr; projmapsub]) = longprodIxtypes [aggrindextype; ixtype]
	in
	let expandgrouplocs = RLMap.mapi (fun grname narrowid ->
		let (dgnew, wideid) = putIdNodeOnTop !changedg narrowid aggrindextype jointtype projmapaggr
		in
		changedg := dgnew;
		wideid
	) grouplocs
	and expandquerylocs = RLMap.map (fun attrloc ->
		let (dgnew, wideid) = putIdNodeOnTop !changedg attrloc ixtype jointtype projmapsub
		in
		changedg := dgnew;
		wideid
	) attrlocs
	in
	let eqnodelocs = RLMap.fold (fun colname grouploc ll ->
		let (dgnew, eqloc) = addNodesToGraph !changedg jointtype [grouploc; RLMap.find colname expandquerylocs] nkIsEq (fun _ -> PortCompare)
		in
		changedg := dgnew;
		eqloc :: ll
	) expandgrouplocs []
	in
	let (dg', expfilterloc) = putIdNodeOnTop !changedg filterloc ixtype jointtype projmapsub
	in
	let (dg'', iseqloc) = addNodesToGraph dg' jointtype (expfilterloc :: eqnodelocs) nkAnd (fun _ -> PortStrictB)
	in
	let longorid = NewName.get ()
	in
	let longornode = {
		nkind = nkLongOr;
		id = longorid;
		inputindextype = jointtype;
		outputindextype = aggrindextype;
		ixtypemap = projmapaggr;
		inputs = PortMap.empty;
	}
	in
	let dg3 = DG.addedge ((identityIndexMap iseqloc jointtype, NewName.get ()), longorid, PortSingleB) (DG.addnode longornode dg'')
	in
	changedg := dg3;
	let filteredNodeLocs = RLMap.map (fun attrloc ->
		let vtype = (DG.findnode attrloc !changedg).nkind.outputtype
		in
		let (dgnew, filterid) = addNodesToGraph !changedg jointtype [iseqloc; attrloc] (nkFilter vtype) (fun x -> if x = 0 then PortSingleB else PortSingle vtype)
		in
		changedg := dgnew;
		filterid
	) expandquerylocs
	in
	let resultlocs = List.fold_right (fun (aggroattrname, aggrokind) mm ->
		let attrloc = RLMap.find aggroattrname filteredNodeLocs
		in
		let vtype = (DG.findnode attrloc !changedg).nkind.outputtype
		in
		let aggroid = NewName.get ()
		in
		let aggrnkind, aggrinport = match aggrokind, vtype with
			| AGMakeBag, VTuple [(_,VTuple dims);(_,vt)] -> nkMakeBag dims vt, PortSingle vt
			| _,_ -> nkAggregate vtype aggrokind, PortSingle vtype
		in
		let aggronode = {
			nkind = aggrnkind;
			id = aggroid;
			inputindextype = jointtype;
			outputindextype = aggrindextype;
			ixtypemap = projmapaggr;
			inputs = PortMap.empty;
		}
		in
		changedg := DG.addedge ((identityIndexMap attrloc jointtype, NewName.get ()), aggroid, aggrinport) (DG.addnode aggronode !changedg);
		RLMap.add aggroattrname aggroid mm
	) aggroattrs grouplocs
	in
	(!changedg, (longorid, resultlocs, aggrindextype))
;;

let rec (convertRAwork : DG.t -> dblocationtype -> raexpressiontype -> DG.t * tablelocationtype) = fun dg0 dblocs -> function
| RATable tblname -> (dg0, RLMap.find tblname dblocs)
| RAFilter (subexp, filterexp) ->
	let (dg', ((oldfilterloc, attrlocs, ixtype) as subloc)) = convertRAwork dg0 dblocs subexp
	in
	let (dg'', addfilterloc) = computeAnyExp dg' subloc filterexp
	in
	let (dg3, newfilterloc) = addNodesToGraph dg'' ixtype [oldfilterloc; addfilterloc] nkAnd (fun _ -> PortStrictB)
	in
	(dg3, (newfilterloc, attrlocs, ixtype))
| RAProject (subexp, keptcols) ->
	let (dg', (filterloc, attrlocs, ixtype)) = convertRAwork dg0 dblocs subexp
	in
	(dg', (filterloc, List.fold_right (fun colname m -> RLMap.add colname (RLMap.find colname attrlocs) m) keptcols RLMap.empty, ixtype))
| RACartesian subexps ->
	let (dg', tbllocs) = List.fold_right (fun subexp (dgacc, prevtbllocs) ->
		let (dg'', currtblloc) = convertRAwork dgacc dblocs subexp
		in
		(dg'', currtblloc :: prevtbllocs)
	) subexps (dg0, [])
	in
	let (jointixtype, projmaps) = longprodIxtypes (List.map (fun (_,_,x) -> x) tbllocs)
	in
	let changedg = ref dg'
	and resattrloc = ref RLMap.empty
	in
	let conjsources = List.map2 (fun (filterloc, tbloc, origixtype) projmap ->
		RLMap.iter (fun colname attrloc ->
			let (newdg, idid) = putIdNodeOnTop !changedg attrloc origixtype jointixtype projmap
			in
			changedg := newdg;
			resattrloc := RLMap.add colname idid !resattrloc
		) tbloc;
		let (newdg, idid) = putIdNodeOnTop !changedg filterloc origixtype jointixtype projmap
		in
		changedg := newdg;
		idid
	) tbllocs projmaps
	in
	let (newdg, resfilterloc) = addNodesToGraph !changedg jointixtype conjsources nkAnd (fun _ -> PortStrictB)
	in 
	(newdg, (resfilterloc, !resattrloc, jointixtype))
(* | RAInnerJoin of (raexpressiontype list) * ((string * string) list) *)
| RANonmatchingJoin (leftexp, rightexp, joinexp) ->
	let (dgtmp, (filterlocleft, attrlocleft, ixtypeleft)) = convertRAwork dg0 dblocs leftexp
	in
	let (dg',(filterlocright, attrlocright, ixtyperight)) = convertRAwork dgtmp dblocs rightexp
	in
	let (jointtype, [projmapleft; projmapright]) = longprodIxtypes [ixtypeleft; ixtyperight]
	and changedg = ref dg'
	in
	let expandedattrstmp = RLMap.fold (fun attrname locleft expattrlocs ->
		let (dg1, leftid) = putIdNodeOnTop !changedg locleft ixtypeleft jointtype projmapleft
		in
		changedg := dg1;
		RLMap.add attrname leftid expattrlocs
	) attrlocleft RLMap.empty
	in
	let expandedattrs = RLMap.fold (fun attrname locright expattrlocs ->
		let (dg2, rightid) = putIdNodeOnTop !changedg locright ixtyperight jointtype projmapright
		in
		changedg := dg2;
		RLMap.add attrname rightid expattrlocs
	) attrlocright expandedattrstmp
	in
	let (dg3, rightfilterid) = putIdNodeOnTop !changedg filterlocright ixtyperight jointtype projmapright
	in
	let (dg4, computationresult) = computeAnyExp dg3 (rightfilterid, expandedattrs, jointtype) joinexp
	in
	let (dg5, alleqid) = addNodesToGraph dg4 jointtype [rightfilterid; computationresult] nkAnd (fun _ -> PortStrictB)
	in
	let longorid = NewName.get ()
	in
	let longornode = {
		nkind = nkLongOr;
		id = longorid;
		inputindextype = jointtype;
		outputindextype = ixtypeleft;
		ixtypemap = projmapleft;
		inputs = PortMap.empty;
	}
	in
	let dg6 = DG.addedge ((identityIndexMap alleqid jointtype, NewName.get ()), longorid, PortSingleB) (DG.addnode longornode dg5)
	in
	let (dg7, withnullsloc) = addNodesToGraph dg6 ixtypeleft [longorid] nkNot (fun _ -> PortSingleB)
	in
	let (dg8, finalfilterloc) = addNodesToGraph dg7 ixtypeleft [filterlocleft; withnullsloc] nkAnd (fun _ -> PortStrictB)
	in
	let (dg9, attrlocboth) = RLMap.fold (fun attrname attrid (dgtmp,attrloctmp) ->
		let vt = (DG.findnode attrid dg8).nkind.outputtype
		in
		let (dgnew, nullloc) = addNodesToGraph dgtmp ixtypeleft [] (nkOperation 0 vt (OPNull vt)) (fun _ -> PortUnstrB)
		in
		(dgnew, RLMap.add attrname nullloc attrloctmp)
	) attrlocright (dg8, attrlocleft)
	in
	(dg9, (finalfilterloc, attrlocboth, ixtypeleft))
| RAUnion (leftexp, rightexp) ->
	let (dgtmp, (filterlocleft, attrlocleft, ixtypeleft)) = convertRAwork dg0 dblocs leftexp
	in
	let (dg',(filterlocright, attrlocright, ixtyperight)) = convertRAwork dgtmp dblocs rightexp
	in
	let jointtype = addIndexTypes ixtypeleft ixtyperight
	in
	let (dg'',filterloc) = putIdNodeOnSum dg' [(filterlocleft,ixtypeleft); (filterlocright,ixtyperight)] jointtype
	in
	let (dgfinal, attrloc) = RLMap.fold (fun attrname locleft (dgcurr, attrloccurr) ->
		let locright = RLMap.find attrname attrlocright
		in
		let (dgnext, oneloc) = putIdNodeOnSum dgcurr [(locleft,ixtypeleft); (locright,ixtyperight)] jointtype
		in
		(dgnext, RLMap.add attrname oneloc attrloccurr)
	) attrlocleft (dg'', RLMap.empty)
	in
	(dgfinal, (filterloc, attrloc, jointtype))
| RAUnionWithDifferentSchema (leftexp, rightexp) ->
	let (dgtmp, (filterlocleft, attrlocleft, ixtypeleft)) = convertRAwork dg0 dblocs leftexp
	in
	let (dg',(filterlocright, attrlocright, ixtyperight)) = convertRAwork dgtmp dblocs rightexp
	in
	let jointtype = addIndexTypes ixtypeleft ixtyperight
	in
	let (dg'',filterloc) = putIdNodeOnSum dg' [(filterlocleft,ixtypeleft); (filterlocright,ixtyperight)] jointtype
	in
	let (dgleft, attrlocleft) = RLMap.fold (fun attrname loc (dgcurr, attrloccurr) ->
		let vt = (DG.findnode loc dgcurr).nkind.outputtype
		in
		let (dg1, nullloc) = addNodesToGraph dgcurr ixtyperight [] (nkOperation 0 vt (OPNull vt)) (fun _ -> raise (Failure "This operation has no inputs"))
		in
		let (dg2, oneloc) = putIdNodeOnSum dg1 [(loc,ixtypeleft); (nullloc, ixtyperight)] jointtype
		in
		(dg2, RLMap.add attrname oneloc attrloccurr)
	) attrlocleft (dg'', RLMap.empty)
	in
	let (dgboth, attrloc) = RLMap.fold (fun attrname loc (dgcurr, attrloccurr) ->
		let vt = (DG.findnode loc dgcurr).nkind.outputtype
		in
		let (dg1, nullloc) = addNodesToGraph dgcurr ixtypeleft [] (nkOperation 0 vt (OPNull vt)) (fun _ -> raise (Failure "This operation has no inputs"))
		in
		let (dg2, oneloc) = putIdNodeOnSum dg1 [(nullloc,ixtypeleft); (loc, ixtyperight)] jointtype
		in
		(dg2, RLMap.add attrname oneloc attrloccurr)
	) attrlocright (dgleft, attrlocleft)
	in
	(dgboth, (filterloc, attrloc, jointtype))
| RAIntersection (leftexp, rightexp) ->
	let (dgtmp, (filterlocleft, attrlocleft, ixtypeleft)) = convertRAwork dg0 dblocs leftexp
	in
	let (dg',(filterlocright, attrlocright, ixtyperight)) = convertRAwork dgtmp dblocs rightexp
	in
	let (jointtype, [projmapleft; projmapright]) = longprodIxtypes [ixtypeleft; ixtyperight]
	and changedg = ref dg'
	in
	let equalitychecks = RLMap.fold (fun attrname locleft attrloceq ->
		let locright = RLMap.find attrname attrlocright
		in
		let (dg1, leftid) = putIdNodeOnTop !changedg locleft ixtypeleft jointtype projmapleft
		in
		let (dg2, rightid) = putIdNodeOnTop dg1 locright ixtyperight jointtype projmapright
		in
		let (dg3, eqnodeid) = addNodesToGraph dg2 jointtype [leftid; rightid] nkIsEq (fun _ -> PortCompare)
		in
		changedg := dg3;
		eqnodeid :: attrloceq
	) attrlocleft []
	in
	let (dg4, rightfilterid) = putIdNodeOnTop !changedg filterlocright ixtyperight jointtype projmapright
	in
	let (dg5, alleqid) = addNodesToGraph dg4 jointtype (rightfilterid :: equalitychecks) nkAnd (fun _ -> PortStrictB)
	in
	let longorid = NewName.get ()
	in
	let longornode = {
		nkind = nkLongOr;
		id = longorid;
		inputindextype = jointtype;
		outputindextype = ixtypeleft;
		ixtypemap = projmapleft;
		inputs = PortMap.empty;
	}
	in
	let dg6 = DG.addedge ((identityIndexMap alleqid jointtype, NewName.get ()), longorid, PortSingleB) (DG.addnode longornode dg5)
	in
	let (dg7, finalfilterloc) = addNodesToGraph dg6 ixtypeleft [filterlocleft; longorid] nkAnd (fun _ -> PortStrictB)
	in
	(dg7, (finalfilterloc, attrlocleft, ixtypeleft))
| RADifference (leftexp, rightexp) ->
	let (dgtmp, (filterlocleft, attrlocleft, ixtypeleft)) = convertRAwork dg0 dblocs leftexp
	in
	let (dg',(filterlocright, attrlocright, ixtyperight)) = convertRAwork dgtmp dblocs rightexp
	in
	let (jointtype, [projmapleft; projmapright]) = longprodIxtypes [ixtypeleft; ixtyperight]
	and changedg = ref dg'
	in
	let equalitychecks = RLMap.fold (fun attrname locleft attrloceq ->
		let locright = RLMap.find attrname attrlocright
		in
		let (dg1, leftid) = putIdNodeOnTop !changedg locleft ixtypeleft jointtype projmapleft
		in
		let (dg2, rightid) = putIdNodeOnTop dg1 locright ixtyperight jointtype projmapright
		in
		let (dg3, eqnodeid) = addNodesToGraph dg2 jointtype [leftid; rightid] nkIsEq (fun _ -> PortCompare)
		in
		changedg := dg3;
		eqnodeid :: attrloceq
	) attrlocleft []
	in
	let (dg4, rightfilterid) = putIdNodeOnTop !changedg filterlocright ixtyperight jointtype projmapright
	in
	let (dg5, alleqid) = addNodesToGraph dg4 jointtype (rightfilterid :: equalitychecks) nkAnd (fun _ -> PortStrictB)
	in
	let longorid = NewName.get ()
	in
	let longornode = {
		nkind = nkLongOr;
		id = longorid;
		inputindextype = jointtype;
		outputindextype = ixtypeleft;
		ixtypemap = projmapleft;
		inputs = PortMap.empty;
	}
	in
	let dg6 = DG.addedge ((identityIndexMap alleqid jointtype, NewName.get ()), longorid, PortSingleB) (DG.addnode longornode dg5)
	in
	let (dg6a, flippedloc) = addNodesToGraph dg6 ixtypeleft [longorid] nkNot (fun _ -> PortSingleB)
	in
	let (dg7, finalfilterloc) = addNodesToGraph dg6a ixtypeleft [filterlocleft; flippedloc] nkAnd (fun _ -> PortStrictB)
	in
	(dg7, (finalfilterloc, attrlocleft, ixtypeleft))
| RANewColumn (subexp, colname, colexp) ->
	let (dgtmp, ((filterloc, attrlocs, ixtype) as tblloctmp)) = convertRAwork dg0 dblocs subexp
	in
	let (dg', newattrloc) = computeAnyExp dgtmp tblloctmp colexp
	in
	(dg', (filterloc, RLMap.add colname newattrloc attrlocs, ixtype))
| RAAggregate (subexp, groupattrs, aggroattrs) ->  (* raexpressiontype * (string list) * ((string * aggregationname) list) *)
	let (dgtmp, tblloctmp) = convertRAwork dg0 dblocs subexp
	in
	onlyAggregation dgtmp tblloctmp groupattrs aggroattrs
| RAAddSortColumn (subexp, newcolname, contractcols, sortcol) -> 
	let (dgtmp, ((filterloc, attrlocs, AITT ixtypecont) as tblloctmp)) = convertRAwork dg0 dblocs subexp
	in
	let getvaluetype dg' colname = (DG.findnode (RLMap.find colname attrlocs) dg').nkind.outputtype
	in
	let sortloc = RLMap.find sortcol attrlocs
	and sortcolvaluetype = getvaluetype dgtmp sortcol
	in
	let changedg = ref dgtmp
	in
	let nodesPerVariant = Array.mapi (fun varIdx varTypes ->
		let variantixtype = AITT [| ixtypecont.(varIdx) |]
		in
		let nodeWithRestrictedIxtype attrloc attrvtype =
			let nnid = NewName.get ()
			in
			let idnode = {
				nkind = nkId attrvtype;
				id = nnid;
				inputs = PortMap.empty;
				inputindextype = variantixtype;
				outputindextype = variantixtype;
				ixtypemap = IxM [| Some ((), 0, Array.init (Array.length ixtypecont.(varIdx)) id) |];
			}
			in
			changedg :=
				(let neweid = NewName.get ()
				in
				print_string (NewName.to_string neweid ^ "\n");
				let ndg = DG.addedge ((IxM [| Some (attrloc, varIdx, Array.init (Array.length ixtypecont.(varIdx)) id) |], neweid),
					nnid, PortSingle attrvtype) (DG.addnode idnode !changedg)
				in
				GrbOptimize.areIndicesInOrderForAEdge ndg (DG.findedge neweid ndg);
				ndg);
			nnid
		in
		let updatedCols = List.fold_right (fun attrname m ->
			RLMap.add attrname (nodeWithRestrictedIxtype (RLMap.find attrname attrlocs) (getvaluetype dgtmp attrname)) m
		) (sortcol :: contractcols) RLMap.empty
		and	updatedFilterLoc = nodeWithRestrictedIxtype filterloc VBoolean
		in
		let nameidxs = Array.mapi (fun dimidx (dimvt, perhapsdimname) ->
			let dimname = (match perhapsdimname with Some x -> x | None -> "")
			in
			let origindextype = AITT [| [|(dimvt, Some dimname)|] |]
			in
			let (dg1, tdnid) = addNodesToGraph !changedg origindextype [] (nkTakeDim dimname dimvt) (fun _ -> PortSingleB)
			in
			let (dg2, idnid) = putIdNodeOnTop dg1 tdnid origindextype variantixtype (IxM [| Some ((), 0, [| dimidx |]) |])
			in
			changedg := dg2;
			(idnid, dimname, dimvt)
		) ixtypecont.(varIdx)
		in
		let (dgwidxtuple, idxtupleid) = addNodesToGraph !changedg variantixtype (Array.to_list (Array.map (fun (x,_,_) -> x) nameidxs)) (nkTuple (Array.to_list (Array.map (fun (_,x,y) -> (x,y)) nameidxs))) (fun nx -> PortOperInput (nx + 1))
		in
		let (dgwsortpair, sortlocx) = addNodesToGraph dgwidxtuple variantixtype [idxtupleid; RLMap.find sortcol updatedCols] (nkTuple [("ixs", (DG.findnode idxtupleid dgwidxtuple).nkind.outputtype);("key", getvaluetype dgwidxtuple sortcol)]) (fun nx -> PortOperInput (nx + 1))
		in
		let updatedColsx = RLMap.add sortcol sortlocx updatedCols
		in
		let (dgnext, (nextfilterloc, nextattrlocs, nextixtype)) = onlyAggregation dgwsortpair (updatedFilterLoc, updatedColsx, variantixtype) contractcols [(sortcol, AGMakeBag)] (* nextixtype is same for all variants *)
		in
		changedg := dgnext;
		(updatedFilterLoc, nextfilterloc, nextattrlocs, variantixtype, nextixtype, nameidxs, updatedCols)
	) ixtypecont
	in
	let sortResPerVariant = Array.mapi (fun varIdx (updatefilterloc, nextfilterloc, locsFromAggro, variantixtype, aggrixtype, varnameidxs, updatedCols) ->
		let bagnodeloc = RLMap.find sortcol locsFromAggro
		and justSortCol = RLMap.find sortcol updatedCols
		in
		let (jointixtype, compmaps) = longprodIxtypes [variantixtype; aggrixtype]
		in
		let sumNodes = Array.mapi (fun i (_, othfilterloc, othLocsFromAggro, othvariantixtype, _, othvarnameidxs, _) ->
			let othbagnodeloc = RLMap.find sortcol othLocsFromAggro
			in
			if i = varIdx then
			begin
				let expvarnameidxs = Array.map (fun (previd, dimname, dimvt) ->
					let (dgnew, idnodeid) = putIdNodeOnTop !changedg previd variantixtype jointixtype (List.nth compmaps 0)
					in
					changedg := dgnew;
					(idnodeid, dimname, dimvt)
				) varnameidxs
				in
				let (dgnew, expbagnodeloc) = putIdNodeOnTop !changedg bagnodeloc aggrixtype jointixtype (List.nth compmaps 1)
				in
				changedg := dgnew;
				let contractpairs = Array.to_list (Array.map (fun (_,x,y) -> (x,y)) varnameidxs)
				in
				let (dgnew, sortnodeloc) = addNodesToGraph 
											!changedg 
											jointixtype 
											(expbagnodeloc :: (List.map (fun (x,_,_) -> x) (Array.to_list expvarnameidxs))) 
											(nkSeqNo contractpairs sortcolvaluetype) 
											(fun nx -> if nx = 0 then PortSingle (VBag (contractpairs, sortcolvaluetype)) else let (_,y1,y2) = expvarnameidxs.(nx - 1) in PortSeqNo (nx, y1, y2))
				in
				changedg := dgnew;
				sortnodeloc
			end else
			begin
				(*let expvarnameidxs = Array.map (fun (previd, dimname, dimvt) ->
					let (dgnew, idnodeid) = putIdNodeOnTop !changedg previd variantixtype jointixtype (List.nth compmaps 0)
					in
					changedg := dgnew;
					(idnodeid, dimname, dimvt)
				) othvarnameidxs *)
				let expjustsortcol = 
					let (dgnew, idnodeid) = putIdNodeOnTop !changedg justSortCol variantixtype jointixtype (List.nth compmaps 0)
					in
					changedg := dgnew;
					idnodeid
				in
				let (dgnew, expbagnodeloc) = putIdNodeOnTop !changedg othbagnodeloc aggrixtype jointixtype (List.nth compmaps 1)
				in
				changedg := dgnew;
				let contractpairs = Array.to_list (Array.map (fun (_,x,y) -> (x,y)) othvarnameidxs)
				in
				let (dgnew, sortnodeloc) = addNodesToGraph !changedg jointixtype [expbagnodeloc; expjustsortcol] (nkNumSmaller contractpairs sortcolvaluetype (i < varIdx)) (fun nx -> if nx = 0 then PortSingle (VBag (contractpairs, sortcolvaluetype)) else PortOrder)
				in
				changedg := dgnew;
				sortnodeloc
			end
		) nodesPerVariant
		in
		let (dg1, cntnodeloc) = addNodesToGraph !changedg jointixtype (Array.to_list sumNodes) (nkOperation (Array.length sumNodes) VInteger OPPlus) (fun nx -> PortOperInput (nx + 1))
		in
		let (dg2, nextExpFilterLoc) = putIdNodeOnTop dg1 nextfilterloc aggrixtype jointixtype (List.nth compmaps 1)
		in
		let (dg3, updateExpFilterLoc) = putIdNodeOnTop dg2 updatefilterloc variantixtype jointixtype (List.nth compmaps 0)
		in
		let (dg3a, joinCondLocs) = List.fold_right (fun contractcol (dgcurr, prevLocs) ->
			let locAtVariant = RLMap.find contractcol updatedCols
			and locAtAggro = RLMap.find contractcol locsFromAggro
			in
			let (dga, upLocAtVariant) = putIdNodeOnTop dgcurr locAtVariant variantixtype jointixtype (List.nth compmaps 0)
			in
			let (dgb, upLocAtAggro) = putIdNodeOnTop dga locAtAggro aggrixtype jointixtype (List.nth compmaps 1)
			in
			let (dgc, eqLoc) = addNodesToGraph dgb jointixtype [upLocAtVariant; upLocAtAggro] nkIsEq (fun _ -> PortCompare)
			in
			(dgc, eqLoc :: prevLocs)
		) contractcols (dg3, [])
		in
		let (dg4, bothFilterLoc) = addNodesToGraph dg3a jointixtype (nextExpFilterLoc :: updateExpFilterLoc :: joinCondLocs) nkAnd (fun _ -> PortStrictB)
		in
		changedg := dg4;
		(bothFilterLoc, cntnodeloc, jointixtype)
	) nodesPerVariant
	in
	let sumixtype = Array.fold_right (fun (_,_,ixt) eixt -> addIndexTypes ixt eixt) sortResPerVariant (AITT [||])
	in
	let (dg5, resfilterloc) = putIdNodeOnSum !changedg (Array.to_list (Array.map (fun (x,y,z) -> (x,z)) sortResPerVariant)) sumixtype
	in
	let (dg6, ressortloc) = putIdNodeOnSum dg5 (Array.to_list (Array.map (fun (x,y,z) -> (y,z)) sortResPerVariant)) sumixtype
	in
	let (_,_,_,_,aggrixtype,_,_) = nodesPerVariant.(0)
	in
	let (origixaggrix,oragmaps) = longprodIxtypes [(AITT ixtypecont); aggrixtype]
	in
	let (dg7, finalattrlocs) = RLMap.fold (fun attrname attrloc (dgcurr, newm) ->
		let (dgnew, newattrloc) = putIdNodeOnTop dgcurr attrloc (AITT ixtypecont) origixaggrix (List.nth oragmaps 0)
		in
		(dgnew, RLMap.add attrname newattrloc newm)
	) attrlocs (dg6, RLMap.singleton newcolname ressortloc)
	in
	(dg7, (resfilterloc, finalattrlocs, sumixtype))
(*
| RAAddSortColumn (subexp, newcolname, contractcols, sortcol) -> 
	let (dgtmp, ((filterloc, attrlocs, ixtype) as tblloctmp)) = convertRAwork dg0 dblocs subexp
	in
	let getvaluetype dg' colname = (DG.findnode (RLMap.find colname attrlocs) dg').nkind.outputtype
	in
	let (imtype, ixToIm, strsToIm) = divideIxtype ixtype contractcols
	and sortloc = RLMap.find sortcol attrlocs
	and sortcolvaluetype = getvaluetype dgtmp sortcol
	and contractcolvaluetypes = List.map (getvaluetype dgtmp) contractcols
	and aggroid = NewName.get ()
	in
	let contractpairs = List.combine contractcols contractcolvaluetypes
	in
	let aggronode = {
		nkind = nkMakeBag contractpairs sortcolvaluetype;
		id = aggroid;
		inputindextype = ixtype;
		outputindextype = imtype;
		ixtypemap = ixToIm;
		inputs = PortMap.empty
	}
	in
	let dg1 = DG.addedge ((identityIndexMap filterloc ixtype, NewName.get ()), aggroid, PortSingleB) (DG.addedge ((identityIndexMap sortloc ixtype, NewName.get ()), aggroid, PortSingle sortcolvaluetype) (DG.addnode aggronode dgtmp))
	in
	let (dg2, expaggroid) = putIdNodeOnTop dg1 aggroid imtype ixtype ixToIm
	in
	let changedg = ref dg2
	in
	let dimnodes = List.map2 (fun ccname ccvt ->
		let tkdnid = NewName.get ()
		and tkdndim = AITT [| [|(ccvt, Some ccname) |] |]
		in
		let tkdn = {
	      	nkind = nkTakeDim ccname ccvt;
	      	id = tkdnid;
	      	inputs = PortMap.empty;
	      	inputindextype = tkdndim;
	      	outputindextype = tkdndim;
	      	ixtypemap = identityIndexMap () tkdndim;
	    }
	    in
	    let (dgnew, exptkdnid) = putIdNodeOnTop (DG.addnode tkdn !changedg) tkdnid tkdndim ixtype (RLMap.find ccname strsToIm)
	    in
	    changedg := dgnew;
		(exptkdnid, (ccname, ccvt))
	) contractcols contractcolvaluetypes
	in
	let dimnodesPorts = Array.of_list (List.map snd dimnodes)
	in
	let (dgnew, sortidxloc) = addNodesToGraph !changedg ixtype (expaggroid :: (List.map fst dimnodes)) (nkSeqNo contractpairs sortcolvaluetype) (fun idx ->
		if idx = 0 then PortSingle (VBag (contractpairs, sortcolvaluetype))
		else let (y1,y2) = dimnodesPorts.(idx - 1) in PortSeqNo (idx, y1, y2)
	)
	in
	(dgnew, (filterloc, RLMap.add newcolname sortidxloc attrlocs, ixtype))
*)
| RALetExp (newtblname, newtblexp, restexp) ->
	let (dg', newtblloc) = convertRAwork dg0 dblocs newtblexp
	in
	convertRAwork dg' (RLMap.add newtblname newtblloc dblocs) restexp
| RARenameCol (oldcolname, newcolname, subexp) ->
	let (dg', (filterloc, attrlocs, ixtype)) = convertRAwork dg0 dblocs subexp
	in
	let colloc = RLMap.find oldcolname attrlocs
	in
	(dg', (filterloc, RLMap.add newcolname colloc (RLMap.remove oldcolname attrlocs), ixtype))
and (computeAnyExp : DG.t -> tablelocationtype -> raanyexp -> DG.t * attrlocationtype) = fun dg0 (existloc, collocs, ((AITT aixt) as ixtype)) -> function
| RAXattribute colname -> (dg0, RLMap.find colname collocs)
| RAXoper (opname, args) ->
	let (dg', arglocs) = List.fold_right (fun onearg (dgacc, prevarglocs) ->
		let (dg'', currargloc) = computeAnyExp dgacc (existloc, collocs, ixtype) onearg
		in
		(dg'', currargloc :: prevarglocs)
	) args (dg0, [])
	in
	let newkind,nports = match opname with
		| OPPlus
		| OPDiv
		| OPMult
		| OPGeoDist
		| OPCeiling
		| OPCoalesce -> let l = List.length args in nkOperation l (DG.findnode (List.hd arglocs) dg').nkind.outputtype opname, (fun i -> PortOperInput (i + 1))
		| OPNeg -> nkOperation 1 (DG.findnode (List.hd arglocs) dg').nkind.outputtype OPNeg, (fun _ -> PortOperInput 1)
		| OPIsEq -> nkIsEq, (fun _ -> PortCompare)
		| OPLessThan -> nkOperation 2 (DG.findnode (List.hd arglocs) dg').nkind.outputtype OPLessThan, (fun i -> PortOperInput (i + 1))
		| OPLessEqual -> nkOperation 2 (DG.findnode (List.hd arglocs) dg').nkind.outputtype OPLessEqual, (fun i -> PortOperInput (i + 1))
		| OPGreaterThan -> nkOperation 2 (DG.findnode (List.hd arglocs) dg').nkind.outputtype OPLessThan, (fun i -> if i = 0 then PortOperInput 2 else PortOperInput 1)
		| OPGreaterEqual -> nkOperation 2 (DG.findnode (List.hd arglocs) dg').nkind.outputtype OPLessEqual, (fun i -> if i = 0 then PortOperInput 2 else PortOperInput 1)
		| OPAnd -> nkAnd, (fun _ -> PortStrictB)
		| OPOr -> nkOr, (fun _ -> PortUnstrB)
		| OPNot -> nkNot, (fun _ -> PortSingleB)
		| OPIntConst x -> nkOperation 0 VInteger opname, (fun _ -> PortUnstrB)
		| OPStringConst s -> nkOperation 0 VString opname, (fun _ -> PortUnstrB)
		| OPRealConst r -> nkOperation 0 VReal opname, (fun _ -> PortUnstrB)
		| OPBoolConst b -> nkOperation 0 VBoolean opname, (fun _ -> PortUnstrB)
		| OPNull vt -> nkOperation 0 vt opname, (fun _ -> PortUnstrB)
		| OPITE -> let vt = (DG.findnode (List.hd (List.tl arglocs)) dg').nkind.outputtype in nkITE vt, (fun i -> if i = 0 then PortSingleB else if i = 1 then PortTrue vt else PortFalse vt)
	in
	addNodesToGraph dg' ixtype arglocs newkind nports
;;

let convertRA dbdesc raexp = 
  let (dg0, dblocs) = makeinputnodes dbdesc
  in
  let (dg, (extloc, attrlocs, ixtype)) = convertRAwork dg0 dblocs raexp
  in
  let changedg = ref dg
  in
  let outpnodeids = RLMap.map (fun origid ->
    let orignode = DG.findnode origid !changedg
    in
    let origvaltype = orignode.nkind.outputtype
    in
  	let (dgnew, newid) = addNodesToGraph !changedg ixtype [extloc; origid] (nkOutput origvaltype) (fun x -> if x = 0 then PortSingleB else (PortSingle origvaltype))
  	in
  	changedg := dgnew;
  	newid
  ) attrlocs
  in
  (!changedg, outpnodeids, ixtype);;

let equalityOfAttributes joinedattrs =
	RAXoper (OPAnd, List.map (fun (sl,sr) -> RAXoper (OPIsEq, [RAXattribute sl; RAXattribute sr])) joinedattrs);;

let leftouterjoin expleft expright checkExpr =
	let tmpnamel = "__tbl_" ^ (NewName.to_string (NewName.get ()))
	and tmpnamer = "__tbl_" ^ (NewName.to_string (NewName.get ()))
	in
	RALetExp (tmpnamel, expleft,
		RALetExp (tmpnamer, expright,
			RAUnion (
				RAFilter (
					RACartesian [RATable tmpnamel; RATable tmpnamer],
					checkExpr
				),
				RANonmatchingJoin (RATable tmpnamel, RATable tmpnamer, checkExpr)
			)
		)
	)
;;

let leftouterjoin_eqOfAttrs expleft expright joinedattrs =
	leftouterjoin expleft expright (equalityOfAttributes joinedattrs)
;;

let rightouterjoin expleft expright checkExpr = leftouterjoin expright expleft checkExpr;;

let rightouterjoin_eqOfAttrs expleft expright joinedattrs =
	leftouterjoin_eqOfAttrs expright expleft joinedattrs
;;

let fullouterjoin expleft expright checkExpr =
	let tmpnamel = "__tbl_" ^ (NewName.to_string (NewName.get ()))
	and tmpnamer = "__tbl_" ^ (NewName.to_string (NewName.get ()))
	in
	RALetExp (tmpnamel, expleft,
		RALetExp (tmpnamer, expright,
			RAUnion (
				RAUnion (
					RAFilter (
						RACartesian [RATable tmpnamel; RATable tmpnamer],
						checkExpr
					),
					RANonmatchingJoin (RATable tmpnamel, RATable tmpnamer, checkExpr)
				),
				RANonmatchingJoin (RATable tmpnamer, RATable tmpnamel, checkExpr)
			)
		)
	)
;;

let fullouterjoin_eqOfAttrs expleft expright joinedattrs =
	fullouterjoin expleft expright (equalityOfAttributes joinedattrs)
;;

