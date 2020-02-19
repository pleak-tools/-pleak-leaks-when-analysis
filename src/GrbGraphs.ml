open GrbCommons;;

module MySet (Ord : Set.OrderedType) =
struct
  include Set.Make(Ord)
  let comparekeys = Ord.compare
  let from_list l = List.fold_right add l empty
  let of_list = from_list
  let tolmap f s = fold (fun x l -> (f x) :: l) s []
  let map f s = fold (fun x -> add (f x)) s empty
  let mapl f s = fold (fun x -> union (from_list (f x))) s empty
  let rec subsetiter f s =
    if is_empty s then f empty else
      let x = choose s
      in let s' = remove x s
      in (subsetiter f s') ; (subsetiter (fun z -> f ((add x) z)) s')
end;;

module MyMap (Ord:Map.OrderedType) =
struct
  include Map.Make(Ord)
  let comparekeys = Ord.compare
  let elemiter xiter f m =
    (fold (fun k e piter g -> xiter (fun y -> piter (fun z -> g ((add k y) z)) ) e) m 
      (fun ff -> ff empty)) f
  let finddef y x m = try find x m with Not_found -> y
  let union m1 m2 = merge 
  	(fun k v1 v2 -> match v1,v2 with
  		| None,None -> None
  		| Some x,_ -> Some x
  		| _, Some y -> Some y
  	) m1 m2
end;;

module type PrintOrdered =
sig
  include Map.OrderedType
  val tostring : t -> string
end;;

module MyNoisyMap (Ord:PrintOrdered) =
struct
  include MyMap(Ord)
  let noisyFind idx m = 
     begin
     print_string ("NoisyMap: searching for " ^ (Ord.tostring idx) ^ "...");
     let res = find idx m
     in print_string " OK\n"; res
     end
end;;

module type PartiallyOrdered =
sig
  include Map.OrderedType
  val lt : t -> t -> bool
  val usecombine : bool
  val combine : t -> t -> t option
end;;

module MySetFromPO (Ord:PartiallyOrdered) =
struct
  include MySet(Ord)
  let maddnocombine elm s =
    if exists (fun e -> Ord.lt elm e) s then s else
    add elm (filter (fun e -> not (Ord.lt e elm)) s)
  let munionnocombine s1 s2 =
    let s1large = filter (fun e -> not (exists (fun e' -> Ord.lt e e') s2)) s1
    and s2large = filter (fun e -> not (exists (fun e' -> Ord.lt e e') s1)) s2
  in union s1large s2large
  let madd elm s = if Ord.usecombine then
  begin
    if exists (fun e -> Ord.lt elm e) s then s else
    let extraels = fold
      (fun selem ins ->
        let ins1 = 
           match (Ord.combine elm selem) with
             None -> ins
           | Some x -> maddnocombine x ins
        in match (Ord.combine selem elm) with
             None -> ins1
           | Some x -> maddnocombine x ins1
      ) (filter (fun e -> not (Ord.lt e elm)) s) (singleton elm)
    in munionnocombine extraels s
  end else maddnocombine elm s
  let munion s1 s2 = if Ord.usecombine then
  begin
    let s1large = filter (fun e -> not (exists (fun e' -> Ord.lt e e') s2)) s1
    and s2large = filter (fun e -> not (exists (fun e' -> Ord.lt e e') s1)) s2
    in
    fold (fun e -> madd e) s2large s1large
  end else munionnocombine s1 s2
end;;

module NewName :
sig
  type idtype = int
  val get : unit -> idtype
  val to_string : idtype -> string
  val from_string : string -> idtype
  val invalid_id : idtype
  val from_int : int -> idtype
end =
struct
  type idtype = int
  let nextid = ref 0
  let get () = nextid := !nextid + 1; !nextid
  let to_string = string_of_int
  let from_string = int_of_string
  let invalid_id = 0
  let from_int i = i
end;;

module IntSet = MySet(struct type t = int let compare = Pervasives.compare end);;

module IdtSet = MySet(struct type t = NewName.idtype let compare = Pervasives.compare end);;

module IntMap = MyMap(struct type t = int let compare = Pervasives.compare end);;

module IdtMap = MyMap(struct type t = NewName.idtype let compare = Pervasives.compare end);;

(* Index types *)

type valuetype =
  NoValue | VUnit | VBoolean | VNaeloob | VInteger | VTimePoint | VReal | VString | VAny | VBag of (string * valuetype) list * valuetype | VTuple of (string * valuetype) list;;
  
(* type leafindextagtype = LIxTUnit | LIxTBool |LIxTNat | LIxTString;; *)

(* type 'a annotindextypetype = IxTLeaf of 'a
						   | IxTSum of 'a annotindextypetype * 'a annotindextypetype
						   | IxTProd of 'a annotindextypetype * 'a annotindextypetype;;
*)

type 'a annotindextypetype = AITT of 'a array array;;

(*
let rec mapannotindex f = function
  | IxTLeaf x -> IxTLeaf (f x)
  | IxTSum (x,y) -> IxTSum (mapannotindex f x, mapannotindex f y)
  | IxTProd (x,y) -> IxTProd (mapannotindex f x, mapannotindex f y);;
*)

let mapannotindex f (AITT i) = AITT (Array.map (Array.map f) i);;

type indextypetype = (valuetype * string option) annotindextypetype;;

(*
type indexmaptype = IxMId
				  | IxMProjL of indexmaptype (* if the domain is a product *)
				  | IxMProjR of indexmaptype (* if the domain is a product *)
				  | IxMCase of indexmaptype * indexmaptype (* if the domain is a sum *)
				  | IxMComps of indexmaptype * indexmaptype (* if the codomain is a product *)
				  | IxMInL if indexmaptype (* if the codomain is a sum *)
				  | IxMInR if indexmaptype (* if the codomain is a sum *)
				  | IxMUndef (* if we know that this branch won't be taken *)
*)

type 'c annotindexmaptype = IxM of ('c * int * int array) option array;;

type indexmaptype = unit annotindexmaptype;;

type connectiontype = NewName.idtype annotindexmaptype * NewName.idtype;;

(*
type enterindextype = EIGuessL of enterindextype | EIGuessR of enterindextype | EIGoL of enterindextype | EIGoR of enterindextype | EITake;;
*)

let isValidIndexMap (AITT domaintype) (AITT rangetype) (IxM  mapping) = 
	let domnumvars = Array.length domaintype
	and rannumvars = Array.length rangetype
	in
	(domnumvars = Array.length mapping) &&
	List.for_all (fun i -> match mapping.(i) with
		| None -> true
		| Some (_, mapvar, prodmap) -> (mapvar >= 0) && (mapvar < rannumvars) && (
			let domvartype = domaintype.(i)
			and ranvartype = rangetype.(mapvar)
			in
			let vartypelen = Array.length ranvartype
			in
			(vartypelen = Array.length prodmap) &&
			( List.for_all (fun j ->
				let x = prodmap.(j)
				in
				(x >= 0) && (x < Array.length domvartype) && ((fst ranvartype.(j)) = (fst domvartype.(x)))
			  ) (intfromto 0 (vartypelen - 1)) )
		)
	) (intfromto 0 (domnumvars - 1));;

(*
let rec isValidIndexMap domaintype rangetype mapping =
  match mapping with
    | IxMUndef -> true
    | IxMId -> (domaintype = rangetype)
    | IxMProjL innerm -> ( match domaintype with
    	| IxTProd (innerd,_) -> isValidIndexMap innerd rangetype innerm
    	| _ -> false )
    | IxMProjR innerm -> ( match domaintype with
    	| IxTProd (_,innerd) -> isValidIndexMap innerd rangetype innerm
    	| _ -> false )
    | IxMCase (innerml,innermr) -> ( match domaintype with
    	| IxTSum (innerdl,innerdr) -> (isValidIndexMap innerdl rangetype innerml) && (isValidIndexMap innerdr rangetype innermr)
    	| _ -> false )
    | IxMComps (innerml,innermr) -> (match rangetype with
    	| IxTProd (innerrl,innerrr) -> (isValidIndexMap domaintype innerrl innerml) && (isValidIndexMap domaintype innerrr innermr)
    	| _ -> false )
    | IxMInL innerml -> (match rangetype with
    	| IxTSum (innerrl,_) -> isValidIndexMap domaintype innerrl innerml
    	| _ -> false )
    | IxMInR innermr -> (match rangetype with
    	| IxTSum (innerrr,_) -> isValidIndexMap domaintype innerrr innermr
    	| _ -> false );;
*)

(*    	
let rec isValidEnterIndex domaintype eival =
  match domaintype,eival with
  	| IxTLeaf _, EITake -> true
  	| IxTSum (dl,_), EIGuessL el -> isValidEnterIndex dl el
  	| IxTSum (_,dr), EIGuessR er -> isValidEnterIndex dr er
  	| IxTProd (dl,_), EIGoL el -> isValidEnterIndex dl el
  	| IxTProd (_,dr), EIGoR er -> isValidEnterIndex dr er
  	| _,_ -> false;;
*)

let isSurjectiveIndexMap (AITT domaintype) (AITT rangetype) (IxM mapping) =
	let hasComp = Array.make (Array.length rangetype) false
	in
	Array.iter (function
		| None -> ()
		| Some (_,x,_) -> Array.set hasComp x true
	  ) mapping;
	Array.fold_right (fun x y -> x && y) hasComp true;;

let addIndexTypes (AITT ixt1) (AITT ixt2) = AITT (Array.append ixt1 ixt2);;

let zeroIndexType () = AITT ([||] );;

let fromZeroIndexMap rangetype = IxM ( [||] );;

let prodIndexTypes (AITT ixt1) (AITT ixt2) = AITT (
	let innerloopsize = Array.length ixt2
	in
	Array.init ((Array.length ixt1) * innerloopsize) (fun i ->
		let x1 = i / innerloopsize
		and x2 = i mod innerloopsize
		in
		Array.append ixt1.(x1) ixt2.(x2)
	)
);;

let unitIndexType () = AITT (Array.make 1 [||] );;

let intoUnitIndexMap (AITT dom) carryVal = IxM (Array.init (Array.length dom) (fun i -> Some (carryVal i, 0, [||] ) ) );;

(*
let addIndexMaps (IxM ((AITT dom1), (AITT ran1), m1)) (IxM ((AITT dom2), (AITT ran2), m2)) =
	IxM ( addIndexTypes (AITT dom1) (AITT dom2), addIndexTypes (AITT ran1) (AITT ran2),
	Array.init ((Array.length dom1) + (Array.length dom2)) (fun i ->
		if i < Array.length dom1
		then m1.(i)
		else
			match m2.(i) with
				| None -> None
				| Some (v,x,l) -> Some (v, x + (Array.length ran1), l)
	));;

let univSumIndexMaps (IxM ((AITT dom1), (AITT ran1), m1)) (IxM ((AITT dom2), (AITT ran2), m2)) =
	if ran1 = ran2 then IxM (addIndexTypes (AITT dom1) (AITT dom2), (AITT ran1), Array.append m1 m2) else raise (Failure "univSumIndexMaps");;
*)

let multIndexMaps comb (AITT dom1) (AITT ran1) (IxM m1) (AITT dom2) (AITT ran2) (IxM m2) = IxM (
	Array.init ((Array.length dom1) * (Array.length dom2)) (fun i ->
		let x1 = i / (Array.length dom2)
		and x2 = i mod (Array.length dom2)
		in
		match m1.(x1), m2.(x2) with
			| None, _ | _, None -> None
			| Some (v1,y1,l1), Some (v2,y2,l2) -> Some (comb v1 v2, y1 * (Array.length ran2) + y2,
				Array.init ((Array.length ran1.(y1)) + (Array.length ran2.(y2))) (fun j ->
				if j < (Array.length ran1.(y1)) then l1.(j) else l2.(j - (Array.length ran1.(y1))) + Array.length dom1.(x1)   ) )
		));;
(*
let univProdIndexMaps comb (IxM ((AITT dom1), (AITT ran1), m1)) (IxM ((AITT dom2), (AITT ran2), m2)) = if dom1 = dom2 then IxM (
	(AITT dom1), prodIndexTypes (AITT ran1) (AITT ran2),
	Array.mapi (fun i domvar -> match m1.(i), m2.(i) with
		| None, _ | _, None -> None
		| Some (v1,y1,l1), Some (v2,y2,l2) -> Some (comb v1 v2, y1 * (Array.length ran2) + y2,
			Array.init ((Array.length ran1.(y1)) + (Array.length ran2.(y2))) (fun j ->
			if j < (Array.length ran1.(y1)) then l1.(j) else l2.(j - (Array.length ran1.(y1)))   ) )
	) dom ) else raise (Failure "univProdIndexMaps");;

let seqCompIndexMaps comb (IxM ((AITT dom1), (AITT ran1), m1)) (IxM ((AITT dom2), (AITT ran2), m2)) = if ran1 = dom2 then IxM (
	(AITT dom1), (AITT ran2),
	Array.mapi (fun i m1var -> match m1var with
		| None -> None
		| Some (v1,y1,l1) -> (match m2.(y1) with
			| None -> None
			| Some (v2,y2,l2) -> Some (comb v1 v2, y2, Array.map (fun z -> l1.(z)) l2 )
	)) m1 );;
*)

let identityIndexMap v (AITT dom) = IxM (
	Array.mapi (fun i domvar ->
		Some (v, i, Array.init (Array.length domvar) id )
	) dom );;

let mapindexmap f (IxM a) = IxM (
	Array.map (function
				| None -> None
				| Some (v, c, m) -> Some (f v, c, m)
			) a );;

let (longprodIxtypes : indextypetype list -> indextypetype * indexmaptype list) = fun ll ->
	let (restype, pairlist) = List.fold_right (fun ixtype (currrestype, currresmaps) ->
		let factorAtLeft = intoUnitIndexMap ixtype (fun _ -> ())
		and factorAtRight = intoUnitIndexMap currrestype (fun _ -> ())
		and newrestype = prodIndexTypes ixtype currrestype
		in
		let newresmaps = List.map (fun (currmap, origtype) -> (multIndexMaps (fun () () -> ()) ixtype (unitIndexType ()) factorAtLeft currrestype origtype currmap, origtype)) currresmaps
		and newixmap = multIndexMaps (fun () () -> ()) ixtype ixtype (identityIndexMap () ixtype) currrestype (unitIndexType ()) factorAtRight
		in (newrestype, (newixmap, ixtype) :: newresmaps)
	) ll (unitIndexType (), [])
	in (restype, List.map fst pairlist);;

module RLMap = MyMap (String);;
module RLSet = MySet (String);;

let (divideIxtype : indextypetype -> string list -> indextypetype * indexmaptype * (indexmaptype RLMap.t)) = fun (AITT ixt) ss0 ->
	let ss = RLSet.of_list ss0
	in
	let coverOneComp a =
		let myss = ref ss
		and resm = ref [||]
		and rest = ref [||]
		in
		Array.iteri (fun idx (vt,tp) ->
			match tp with
			|	None -> (resm := Array.append !resm [|idx|]; rest := Array.append !rest [|(vt,tp)|])
			|	Some s -> (if RLSet.mem s !myss then begin myss := RLSet.remove s !myss end else begin resm := Array.append !resm [|idx|]; rest := Array.append !rest [|(vt,tp)|] end)
		) a;
		if RLSet.is_empty !myss then (Some (!rest, !resm)) else None
	in
	let allvalues = Array.map coverOneComp ixt
	in
	let restype = Array.map (fun v ->
		match v with
		| Some (vv,_) -> vv
		| None -> raise (Failure "divideIxType")
	) allvalues
	and resmap = Array.mapi (fun idx v -> 
		match v with
		| Some (_,vv) -> Some ((), idx, vv)
		| None -> raise (Failure "divideIxType")
	) allvalues
	in
	let findidx f a =
		let res = ref None
		in
		Array.iteri (fun idx x ->
			match !res with
			| None -> ( if f x then res := Some idx else () )
			| Some _ -> ()
		) a;
		!res
	in
	let mkMap s = IxM (
		Array.map (fun a ->
			match findidx (fun (_,tp) -> match tp with None -> false | Some s' -> s = s' ) a with
			| None -> None
			| Some v -> Some ((), 0, [|v|])
		) ixt )
	in
	let resattrmap = List.fold_right (fun s m ->
		RLMap.add s (mkMap s) m
	) ss0 RLMap.empty
	in
	(AITT restype, IxM resmap, resattrmap);;

(*
let rec composeIndexMaps f g = (* computes f \circ g. I.e. codomain(g) = domain(f) *)
  match (f,g) with
    | (_, IxMId) -> Some f
    | (IxMid, _) -> Some g
    | (IxMUndef, _) -> Some IxMUndef
    | (_, IxMUndef) -> Some IxMUndef
    | (_, IxMProjL innerg) -> (match composeIndexMaps f innerg with Some h -> Some (IxMProjL h) | None -> None)
    | (_, IxMProjR innerg) -> (match composeIndexMaps f innerg with Some h -> Some (IxMProjR h) | None -> None)
    | (_, IxMCase (innergl,innergr)) -> (match (composeIndexMaps f innergl, composeIndexMaps f innergl) with (Some h1, Some h2) -> Some (IxMCase (h1,h2)) | _ -> None)
    | (IxMComps (prodfl,prodfr), _) -> (match (composeIndexMaps prodfl g, composeIndexMaps prodfr g) with (Some h1, Some h2) -> Some (IxMComps (h1,h2)) | _ -> None)
    | (IxMInL sumfl, _) -> (match composeIndexMaps sumfl g with Some h -> Some (IxMInL h) | None -> None)
    | (IxMInR sumfr, _) -> (match composeIndexMaps sumfr g with Some h -> Some (IxMInR h) | None -> None)
    | (IxProjL innerf, IxMComps (prodgl,_)) -> composeIndexMaps innerf prodgl
    | (IxProjR innerf, IxMComps (_,prodgr)) -> composeIndexMaps innerf prodgr
    | (IxMCase (innerfl,_), IxMInL sumgl) -> composeIndexMaps innerfl sumgl
    | (IxMCase (_,innerfr), IxMInR sumgr) -> composeIndexMaps innerfr sumgr
    | _ -> None;;
*)
(*
let rec isSurjectiveIndexMap domaintype rangetype mapping =
  match mapping with
    | IxMId -> true
    
*)

let composeIxM (IxM lf) nid (IxM uf) = IxM (
	Array.mapi (fun lidx -> function
		| None -> None
		| Some (nid', cmp, backmap) as sumchoice -> if nid <> nid' then sumchoice else
		begin
			match uf.(cmp) with
				| None -> None
				| Some (srcid, cmp', backmap') -> Some (srcid, cmp', Array.map (fun i -> backmap.(i)) backmap')
		end
	) lf
);;




let conncomp (c1,id1) (c2,id2) = Pervasives.compare c1 c2;;

module ConnectionSet = MySet(
struct 
  type t = connectiontype 
  let compare = conncomp
end);;

module ConnectionMap = MyMap(
struct
  type t = connectiontype
  let compare = conncomp
end);;

let rec string_of_valuetype = function
  NoValue -> "no value"
| VBoolean -> "boolean"
| VNaeloob -> "inv-boolean"
| VInteger -> "integer"
| VTimePoint -> "timepoint"
| VReal -> "real"
| VString -> "string"
| VAny -> "any"
| VUnit -> "unit"
| VBag (svl, rangetype) -> "[" ^ (String.concat "; " (List.map (fun (s,vt) -> "(" ^ s ^ "," ^ (string_of_valuetype vt) ^ ")") svl)) ^ "] -> " ^ (string_of_valuetype rangetype)
| VTuple svl -> "[" ^ (String.concat "; " (List.map (fun (s,vt) -> "(" ^ s ^ "," ^ (string_of_valuetype vt) ^ ")") svl)) ^ "]"
;;

let inclvalue x y = match x,y with  (* strict inclusion *)
| x, VAny -> x <> VAny
| _,_ -> false;;

let ns_inclvalue x y = (x=y) || (inclvalue x y);;

type operationname = OPPlus | OPNeg | OPMult | OPIsEq | OPLessThan | OPLessEqual | OPGreaterThan | OPGreaterEqual | OPAnd | OPOr | OPNot | OPDiv | OPPow | OPIntConst of int | OPStringConst of string | OPRealConst of float | OPBoolConst of bool | OPTimePointConst of (int,int) either | OPNull of valuetype | OPGeoDist | OPCeiling | OPCoalesce | OPITE | OPTuple of string list | OPProject of string | OPOrder of bool;;

let string_of_opname = function
| OPPlus -> "+"
| OPNeg -> "neg"
| OPMult -> "*"
| OPIsEq -> "=?"
| OPLessThan -> "<?"
| OPLessEqual -> "<=?"
| OPGreaterThan -> ">?"
| OPGreaterEqual -> ">=?"
| OPAnd -> "&&"
| OPOr -> "||"
| OPNot -> "!"
| OPDiv -> "/"
| OPPow -> "^"
| OPGeoDist -> "distance"
| OPCoalesce -> "coalesce"
| OPCeiling -> "ceiling"
| OPIntConst x -> (string_of_int x) ^ "C"
| OPStringConst s -> "\\\"" ^ s ^ "\\\""
| OPRealConst r -> (string_of_float r) ^ "C"
| OPBoolConst b -> (string_of_bool b)
| OPNull vt -> "NULL (" ^ (string_of_valuetype vt) ^ ")"
| OPITE -> "if-then-else"
| OPTuple ll -> "[" ^ (string_of_list id (intersperse ll ", ")) ^ "]-tuple"
| OPProject s -> "Pr " ^ s
| OPOrder b -> "CNT(" ^ (if b then "LE" else "LT") ^ ")"
| OPTimePointConst vx -> (match vx with Left x -> (string_of_int x) ^ "L" | Right x -> (string_of_int x) ^ "R")
;;

type aggregationname = AGMax | AGMin | AGSum | AGCount | AGExist | AGAverage | AGMakeBag;;

let string_of_aggrname = function
| AGMax -> "max"
| AGMin -> "min"
| AGSum -> "sum"
| AGCount -> "count"
| AGExist -> "exist"
| AGMakeBag -> "bag"
| AGAverage -> "avg"
;;

type nodename = 
| NNTakeDim of string
| NNInput of string * valuetype * bool
| NNInputExists of string
| NNId
| NNAnd of bool
| NNIsEq
| NNIsNEq
| NNLongOr of bool
| NNLongAnd of bool
| NNMakeBag of (string * valuetype) list
| NNSeqNo
| NNNot
| NNNotFlip of bool (* the argument indicates whether the output is a VBoolean (true) or a VNaeloob (false) *)
| NNFilter of valuetype
| NNOperation of operationname
| NNAggregate of aggregationname
| NNOutput of RLSet.t (* description of where this output came from *)
| NNOr of bool
| NNTrue of bool
| NNFalse of bool
| NNZeroTimePoint
| NNError
| NNITE of valuetype
| NNDimEq
| NNEqualDims of (int * int) list
| NNTuple of (string * valuetype) list
| NNProj of int * (string * valuetype) list
| NNNumSmaller of bool
| NNMaximum
| NNSum
| NNLongMerge of valuetype
| NNMerge of valuetype
| NNGeneric of string * int
| NNAddrGen of NewName.idtype * int * int
| NNTimePoint of string * int
;;

type portsize = PortBounded of int | PortUnbounded;;

type portname = 
| PortSingle of valuetype
| PortMulti of valuetype
| PortSingleB of bool  (* "true" means the input is a VBoolean *)
| PortUSingleB
| PortOperInput of int
| PortCompare
| PortStrictB of bool
| PortUnstrB of bool
| PortSeqNo of int * string * valuetype
| PortTrue of valuetype
| PortFalse of valuetype
| PortOrder
;;

let string_of_portname = function
| PortSingle vt -> "PortSingle(" ^ (string_of_valuetype vt) ^ ")"
| PortMulti vt -> "PortMulti(" ^ (string_of_valuetype vt) ^ ")"
| PortSingleB b -> "PortSingleB(" ^ (string_of_bool b) ^ ")"
| PortUSingleB -> "PortUSingleB"
| PortStrictB b -> "PortStrictB(" ^ (string_of_bool b) ^ ")"
| PortUnstrB b -> "PortUnstrB(" ^ (string_of_bool b) ^ ")"
| PortCompare -> "PortCompare"
| PortOperInput x -> "PortOperInput(" ^ (string_of_int x) ^ ")"
| PortSeqNo (i,s,_) -> "PortSeqNo(" ^ (string_of_int i) ^ ":" ^ s ^ ")"
| PortTrue vt -> "PortTrue(" ^ (string_of_valuetype vt) ^ ")"
| PortFalse vt -> "PortFalse(" ^ (string_of_valuetype vt) ^ ")"
| PortOrder -> "PortOrder"
;;

type portoptions =
  POptStrict | POptInjective;;

module PortOptSet = MySet(struct type t = portoptions let compare = Pervasives.compare end);;

type colortype = int * int * int;;

type porttype = {
  inputkind : valuetype;
  inputnum : portsize;
  inputopts : PortOptSet.t;
  wirename : string;
  wirecolor : colortype;
  printbold : bool;
};;

let portdesc pn = 
  let cdepcol = (0,0,255)
  and defdesc = { 
    inputkind = VAny; 
    inputnum = PortBounded 1;
    inputopts = PortOptSet.singleton POptStrict;
    wirename = "";
    wirecolor = (0,0,0);
    printbold = true;
  }
  in match pn with
| PortFalse vt	-> { defdesc with inputkind = vt; wirename = "F"; inputopts = PortOptSet.empty }
| PortTrue vt	-> { defdesc with inputkind = vt; wirename = "T"; inputopts = PortOptSet.empty }
| PortSingle vt	-> { defdesc with inputkind = vt }
| PortMulti vt	-> { defdesc with inputkind = vt; inputnum = PortUnbounded; inputopts = PortOptSet.empty }
| PortSingleB b	-> { defdesc with inputkind = if b then VBoolean else VNaeloob; wirecolor = cdepcol; printbold = false; wirename = "C" }
| PortUSingleB	-> { defdesc with inputkind = VBoolean; wirecolor = cdepcol; printbold = false; wirename = "C"; inputopts = PortOptSet.empty }
| PortStrictB b	-> { defdesc with inputkind = if b then VBoolean else VNaeloob; inputnum = PortUnbounded; wirecolor = cdepcol; printbold = false }
| PortUnstrB b	-> { defdesc with inputkind = if b then VBoolean else VNaeloob; inputnum = PortUnbounded; inputopts = PortOptSet.empty; wirecolor = cdepcol; printbold = false }
| PortCompare	-> { defdesc with inputkind = VAny; inputnum = PortUnbounded } (* was "PortBounded 2"*)
| PortOperInput n  -> { defdesc with wirename = string_of_int n; inputkind = VAny }
| PortSeqNo (i,s,vt) -> { defdesc with inputkind = vt; wirename = (string_of_int i) ^ ":" ^ s }
| PortOrder		-> { defdesc with wirename = "O" }
;;

type nodeoptions =
  NOptInput;;

module ComparablePort =
struct
  type t = portname
  let compare = Pervasives.compare
end;;

module PortSet = MySet(ComparablePort);;

module PortMap = 
struct
  include Map.Make(ComparablePort)
  let add_list l =
  List.fold_right (fun (pname,conn) f ->
    match (portdesc pname).inputnum with
      PortBounded _ -> (
        try
          let cmap = (match find pname f with Left x -> x | _ -> assert false) in
          let cmap' = (
          try
            let cval = ConnectionMap.find conn cmap in
            ConnectionMap.add conn (cval + 1) cmap
          with Not_found ->
            ConnectionMap.add conn 1 cmap
          ) in
          add pname (Left cmap') f
        with Not_found ->
          add pname (Left (ConnectionMap.add conn 1 ConnectionMap.empty)) f
      )
    | PortUnbounded -> (
        try
          let cset = (match find pname f with Right x -> x | _ -> assert false) in
          add pname (Right (ConnectionSet.add conn cset)) f
        with Not_found ->
          add pname (Right (ConnectionSet.singleton conn)) f
      )
  ) l;;
  let from_list l = add_list l empty;;
end;;

type nodekind = {
  contracts : bool;    (* LongOr and LongMux *)
  makesbottom : bool;  (* False and Error nodes *)
  inadvview : bool;    (* Send, Begin, End, TTT nodes *)
  isinputnode : bool;   (* Receive, RS, Req nodes *)
  nofail : bool;
  ports : PortSet.t;
  outputtype : valuetype;
  nodeintlbl : nodename;
  nodelabel : indexmaptype -> string;
  nodecolor : colortype;
  nodetextcolor : colortype;
  boldborder : bool;
};;

type nodetype = {
  nkind : nodekind;
  id : NewName.idtype;
  inputs : ((int ConnectionMap.t, ConnectionSet.t) either) PortMap.t;
  inputindextype : indextypetype;
  outputindextype : indextypetype;
  ixtypemap : indexmaptype;
};;

let nkInput vt inpname isUnique = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = true;
  nofail = false;
  ports = PortSet.empty;
  outputtype = vt;
  nodeintlbl = NNInput (inpname,vt,isUnique);
  nodelabel = (fun _ -> "Input" ^ (if isUnique then "(U)" else "") ^ " " ^ inpname);
  nodecolor = (255,255,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkInputExists tblname = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = true;
  nofail = false;
  ports = PortSet.empty;
  outputtype = VBoolean;
  nodeintlbl = NNInputExists tblname;
  nodelabel = (fun _ -> "Exists: " ^ tblname);
  nodecolor = (255,255,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkTakeDim enteridx cval = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = false;
  ports = PortSet.empty;
  outputtype = cval;
  nodeintlbl = NNTakeDim enteridx;
  nodelabel = (fun _ -> ("TakeDim " ^ enteridx));
  nodecolor = (255,255,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkOutput cval inpdesc = {
  contracts = false;
  makesbottom = false;
  inadvview = true;
  isinputnode = false;
  nofail = false;
  ports = PortSet.from_list [PortSingleB true; PortSingle cval];
  outputtype = NoValue;
  nodeintlbl = NNOutput inpdesc;
  nodelabel = (fun _ -> "Out[" ^ (String.concat ", " (RLSet.elements inpdesc)) ^ "]");
  nodecolor = (192,128,0);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkOperation i vt opname = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list (List.map (fun k -> PortOperInput k) (intfromto 1 i));
  outputtype = vt;
  nodeintlbl = NNOperation opname;
  nodelabel = (fun _ -> "OP:" ^ (string_of_opname opname));
  nodecolor = (128,192,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkAddrGen place dimnum inpnum = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list (List.map (fun k -> PortOperInput k) (intfromto 1 inpnum));
  outputtype = VInteger;
  nodeintlbl = NNAddrGen (place, dimnum, inpnum);
  nodelabel = (fun _ -> "Addr" ^ (NewName.to_string place) ^ "(" ^ (string_of_int dimnum) ^ ")");
  nodecolor = (128,128,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkTimePoint place inpnum = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.add (PortSingle VTimePoint) (PortSet.from_list (List.map (fun k -> PortOperInput k) (intfromto 1 inpnum)));
  outputtype = VTimePoint;
  nodeintlbl = NNTimePoint (place, inpnum);
  nodelabel = (fun _ -> "TP_" ^ place);
  nodecolor = (128,128,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkTuple svtl = {
	contracts = false;
	makesbottom = false;
	inadvview = false;
	isinputnode = false;
	nofail = true;
    ports = PortSet.from_list (List.map (fun k -> PortOperInput k) (intfromto 1 (List.length svtl)));
	outputtype = VTuple svtl;
	nodeintlbl = NNTuple svtl;
	nodelabel = (fun _ -> "[" ^ (string_of_list id (intersperse (List.map fst svtl) ",")) ^ "]");
    nodecolor = (128,192,255);
    nodetextcolor = (0,0,0);
    boldborder = true;
};;

let nkProj i svtl = {
	contracts = false;
	makesbottom = false;
	inadvview = false;
	isinputnode = false;
	nofail = true;
	ports = PortSet.singleton (PortSingle (VTuple svtl));
	outputtype = snd (List.nth svtl (i-1));
	nodeintlbl = NNProj (i,svtl);
	nodelabel = (fun _ -> "Proj " ^ (string_of_int i));
    nodecolor = (128,192,255);
    nodetextcolor = (0,0,0);
    boldborder = true;
};;

let nkError = {
  contracts = false;
  makesbottom = true;
  inadvview = false;
  isinputnode = false;
  nofail = false;
  ports = PortSet.empty;
  outputtype = VAny;
  nodeintlbl = NNError;
  nodelabel = (fun _ -> "Error");
  nodecolor = (255,255,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkZeroTimePoint = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = false;
  ports = PortSet.empty;
  outputtype = VTimePoint;
  nodeintlbl = NNZeroTimePoint;
  nodelabel = (fun _ -> "0L");
  nodecolor = (255,255,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkId vtype = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list [PortSingle vtype];
  outputtype = vtype;
  nodeintlbl = NNId;
  nodelabel = (fun _ -> "Id");
  nodecolor = (128,192,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkGeneric name isGuard argc = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list (List.map (fun i -> PortOperInput i) (intfromto 1 argc));
  outputtype = if isGuard then VBoolean else VAny;
  nodeintlbl = NNGeneric (name, argc);
  nodelabel = (fun _ -> name);
  nodecolor = (128,192,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkMaximum vtype = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list [PortMulti vtype];
  outputtype = vtype;
  nodeintlbl = NNMaximum;
  nodelabel = (fun _ -> "MAX");
  nodecolor = (128,128,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkSum vtype = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list [PortMulti vtype];
  outputtype = vtype;
  nodeintlbl = NNSum;
  nodelabel = (fun _ -> "+");
  nodecolor = (128,192,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkMerge vtype = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list [PortMulti vtype];
  outputtype = vtype;
  nodeintlbl = NNMerge vtype;
  nodelabel = (fun _ -> "Merge");
  nodecolor = (255,255,0);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkEqualDims vtype dl = {
  contracts = true;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list [PortSingle vtype];
  outputtype = vtype;
  nodeintlbl = NNEqualDims dl;
  nodelabel = (fun _ -> "EqualDims " ^ (String.concat ", " (List.map (fun (x,y) -> (string_of_int x) ^ "=" ^ (string_of_int y)) dl ) ) );
  nodecolor = (255,128,0);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkITE vtype = {
  contracts = false;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list [PortTrue vtype; PortFalse vtype; PortSingleB true];
  outputtype = vtype;
  nodeintlbl = NNITE vtype;
  nodelabel = (fun _ -> "if-then-else");
  nodecolor = (128,192,255);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkAnd = {
  (nkId VBoolean) with
  ports = PortSet.singleton (PortStrictB true);
  outputtype = VBoolean;
  nodeintlbl = NNAnd true;
  nodelabel = (fun _ -> "and");
  nodecolor = (0,255,0);
  boldborder = false;
};;

let nkAndDT = {
  (nkId VNaeloob) with
  ports = PortSet.singleton (PortUnstrB false);
  outputtype = VNaeloob;
  nodeintlbl = NNAnd false;
  nodelabel = (fun _ -> "and");
  nodecolor = (255,0,0);
  boldborder = false;
};;

let nkLongMerge vtype = {
  (nkId vtype) with
  contracts = true;
  ports = PortSet.singleton (PortSingle vtype);
  outputtype = vtype;
  nodeintlbl = NNLongMerge vtype;
  nodelabel = (fun _ -> "Merge(L)");
  nodecolor = (255,255,0);
};;

let nkOr = {
  nkAnd with
  ports = PortSet.singleton (PortUnstrB true);
  nodeintlbl = NNOr true;
  nodelabel = (fun _ -> "or");
  nodecolor = (0,255,0);
};;

let nkOrDT = {
  nkAndDT with
  ports = PortSet.singleton (PortStrictB false);
  nodeintlbl = NNOr false;
  nodelabel = (fun _ -> "or");
  nodecolor = (255,0,0);
};;

let nkNot = {
  nkOr with
  ports = PortSet.singleton PortUSingleB;
  nodeintlbl = NNNot;
  nodelabel = (fun _ -> "NOT");
  nodecolor = (255,255,0);
};;

let nkNotFlip b = {
  nkOr with
  ports = PortSet.singleton (PortSingleB (not b));
  nodeintlbl = NNNotFlip b;
  outputtype = if b then VBoolean else VNaeloob;
  nodelabel = (fun _ -> "not");
  nodecolor = if b then (0,255,0) else (255,0,0);
};;

let nkTrue = {
  nkAnd with
  ports = PortSet.empty;
  nodeintlbl = NNTrue true;
  nodelabel = (fun _ -> "true");
  nodecolor = (255,255,255);
};;

let nkTrueDT = {
  nkAndDT with
  makesbottom = true;
  nofail = false;
  ports = PortSet.empty;
  nodeintlbl = NNTrue false;
  nodelabel = (fun _ -> "true");
  nodecolor = (0,0,0);
  nodetextcolor = (255,255,255);
};;

let nkDimEq = {nkTrue with nodeintlbl = NNDimEq; nodelabel = (fun _ -> "DimEq")};;

let nkFalse = {
  nkAnd with
  makesbottom = true;
  nofail = false;
  ports = PortSet.empty;
  nodeintlbl = NNFalse true;
  nodelabel = (fun _ -> "false");
  nodecolor = (255,255,255);
};;

let nkFalseDT = {
	nkTrue with
	nodeintlbl = NNFalse true;
	outputtype = VNaeloob;
	nodelabel = (fun _ -> "false");
	nodecolor = (0,0,0);
	nodetextcolor = (255,255,255);
};;

let nkFilter t = {
  (nkId t) with
  nofail = false;
  ports = PortSet.from_list [PortSingleB true; PortSingle t];
  outputtype = t;
  nodeintlbl = NNFilter t;
  nodelabel = (fun _ -> (string_of_valuetype t) ^ " filter");
  nodecolor = (128,128,255);
  boldborder = false;
};;

let nkIsEq = {
  (nkId VBoolean) with
  nofail = false;
  ports = PortSet.singleton PortCompare;
  nodeintlbl = NNIsEq;
  nodelabel = (fun _ -> "=?");
};;

let nkIsNEq = {
  nkIsEq with
  nodeintlbl = NNIsNEq;
  nodelabel = (fun _ -> "!=?");
};;

let nkLongOr = {
  nkAnd with
  contracts = true;
  ports = PortSet.singleton (PortSingleB true);
  nodeintlbl = NNLongOr true;
  nodelabel = (fun _ -> "ooor");
  nodecolor = (0,255,0);
};;

let nkLongOrDT = {
  nkAndDT with
  contracts = true;
  ports = PortSet.singleton (PortSingleB false);
  nodeintlbl = NNLongOr false;
  nodelabel = (fun _ -> "ooor");
  nodecolor = (255,0,0);
};;

let nkLongAnd = {
  nkAnd with
  contracts = true;
  ports = PortSet.singleton (PortSingleB true);
  nodeintlbl = NNLongAnd true;
  nodelabel = (fun _ -> "aaand");
  nodecolor = (0,255,0);
};;

let nkLongAndDT = {
  nkAndDT with
  contracts = true;
  ports = PortSet.singleton (PortSingleB false);
  nodeintlbl = NNLongAnd false;
  nodelabel = (fun _ -> "aaand");
  nodecolor = (255,0,0);
};;

let nkMakeBag dims vt = {
  contracts = true;
  makesbottom = false;
  inadvview = false;
  isinputnode = false;
  nofail = true;
  ports = PortSet.from_list [(*PortSingleB;*) PortSingle vt];
  outputtype = VBag (dims,vt);
  nodeintlbl = NNMakeBag dims;
  nodelabel = (fun _ -> "BagOf " ^ (String.concat "," (List.map fst dims)));
  nodecolor = (192,128,0);
  nodetextcolor = (0,0,0);
  boldborder = true;
};;

let nkSeqNo dims vt = {
	contracts = false;
	makesbottom = false;
	inadvview = false;
	isinputnode =false;
	nofail = false;
	ports = PortSet.union (PortSet.singleton (PortSingle (VBag (dims,vt)))) (PortSet.from_list (List.mapi (fun i (s,vt) -> PortSeqNo (i+1,s,vt)) dims));
	nodeintlbl = NNSeqNo;
	outputtype = VInteger;
	nodelabel = (fun _ -> "SeqNo");
    nodecolor = (192,128,0);
    nodetextcolor = (0,0,0);
    boldborder = true;
};;

let nkNumSmaller dims vt withEqual = {
	contracts = false;
	makesbottom = false;
	inadvview = false;
	isinputnode =false;
	nofail = false;
	ports = PortSet.add PortOrder (PortSet.singleton (PortSingle (VBag (dims,vt))));
	nodeintlbl = NNNumSmaller withEqual;
	outputtype = VInteger;
	nodelabel = (fun _ -> if withEqual then "CNT(LE)" else "CNT(LT)");
    nodecolor = (192,128,0);
    nodetextcolor = (0,0,0);
    boldborder = true;
};;

let nkAggregate vt aggrname = {
  nkIsEq with
  contracts = true;
  nofail = true;
  ports = PortSet.from_list [PortSingle vt];
  outputtype = vt;
  nodeintlbl = NNAggregate aggrname;
  nodelabel = (fun _ -> "Aggr (" ^ (string_of_aggrname aggrname) ^ ")");
  nodecolor = (150,120,90);
};;

  let connectionsources (IxM conns) =
  	Array.fold_right (function
  					| None -> id
  					| Some (src, _, _) -> IdtSet.add src
  				) conns IdtSet.empty;;
  
  let isEmptyConnection connmap = IdtSet.is_empty (connectionsources connmap);;
  
module DG = (
struct
  type t = {
    tnodes : nodetype IdtMap.t;
    tedges : (connectiontype * NewName.idtype * portname) IdtMap.t;
    toutes : IdtSet.t IdtMap.t
  };;
  
  let hasnode nid gr = IdtMap.mem nid gr.tnodes;;
  
  let findnode nid gr = IdtMap.find nid gr.tnodes;;
  
  let foldnodes f gr v0 = IdtMap.fold (fun _ n v -> f n v) gr.tnodes v0;;
  
  let nodefoldedges f n r0 =
    PortMap.fold (fun prt pedges intm' ->
      if PortSet.mem prt n.nkind.ports then
      match pedges with
        Left emap ->
          ConnectionMap.fold (fun ec card -> funcpow card (f (ec,n,prt))
          ) emap intm'
      | Right eset ->
          ConnectionSet.fold (fun ec -> f (ec,n,prt)
          ) eset intm'
      else (print_string ("Node " ^ (NewName.to_string n.id) ^ " has edge to port " ^ (string_of_portname prt) ^ "!\n" ); intm')
    ) n.inputs r0;;

  let foldedges f = foldnodes (nodefoldedges f);;
  
  let foldedgesources f (conns,_) v0 =
  	IdtSet.fold f (connectionsources conns) v0;;
  
  let removeConnectionSource (IxM conns) src =
  	IxM (Array.map (function
  								| None -> None
  								| (Some (src', _, _)) as smth -> if src' = src then None else smth
  							) conns );;
  
  let updatenodeconnections n applyOnCon =
  	let newports = PortMap.fold (fun prtname conns ->
  		let newconns = match conns with 
  			| Left cmap -> Left (ConnectionMap.fold (fun (cc, connid) cnt ->
  			  	let newcc = applyOnCon (cc, connid)
  			  	in
  			  	if isEmptyConnection newcc then id else
			  	ConnectionMap.add (newcc, connid) cnt) cmap ConnectionMap.empty)
			| Right cset ->
				Right ( ConnectionSet.fold (fun (cc, connid) ->
				let newcc = applyOnCon (cc, connid)
  			    in
  			    if isEmptyConnection newcc then id else
			    ConnectionSet.add (newcc, connid)) cset ConnectionSet.empty)
  		in
  		PortMap.add prtname newconns) n.inputs PortMap.empty
  	in
  	{n with inputs = newports};;
  
  let remnode nid gr =
    try
      let n = IdtMap.find nid gr.tnodes
      in
      (* remove edges incoming to n *)
      let (tedges',toutes') = nodefoldedges (fun ((conn,eid),_,tgtport) (tedgescurr,toutescurr) ->
      	let tedgesnext = IdtMap.remove eid tedgescurr
      	and toutesnext = IdtSet.fold (fun csourceid ttt -> let ccss = IdtMap.find csourceid ttt in IdtMap.add csourceid (IdtSet.remove eid ccss) ttt) (connectionsources conn) toutescurr
      	in (tedgesnext, toutesnext)
      ) n (gr.tedges, gr.toutes)
      in
      (* remove edges going out of n *)
      let (tnodes'',tedges'',toutes'') = IdtSet.fold (fun eid (tnodescurr, tedgescurr, toutescurr) ->
      	let ((conn,_),tgtid,tgtport) = IdtMap.find eid tedgescurr
      	in
      	let newconn = removeConnectionSource conn nid
      	and tgtnode = IdtMap.find tgtid tnodescurr
      	in
      	let newtgtnode = updatenodeconnections tgtnode (fun (c,_) -> removeConnectionSource c nid)
      	in
      	let tnodesnext = IdtMap.add tgtid newtgtnode tnodescurr
      	and toutesnext = (* IdtMap.add tgtid (IdtSet.remove eid (IdtMap.find tgtid toutescurr)) *) toutescurr
      	and tedgesnext = if isEmptyConnection newconn then IdtMap.remove eid tedgescurr else IdtMap.add eid ((newconn,eid),tgtid,tgtport) tedgescurr
      	in
      	(tnodesnext, tedgesnext, toutesnext)
      ) (IdtMap.find nid gr.toutes) (gr.tnodes, tedges', toutes')
      in
      {
        tnodes = IdtMap.remove nid tnodes'';
        tedges = tedges'';
        toutes = IdtMap.remove nid toutes''
      }
    with Not_found -> gr;;
  
  let empty = {
    tnodes = IdtMap.empty;
    tedges = IdtMap.empty;
    toutes = IdtMap.empty
  };;
  
  let findedge eid gr =
    let (x,y,z) = IdtMap.find eid gr.tedges
    in (x, IdtMap.find y gr.tnodes, z);;
  
  let remedge eid gr =
    let ((cmap,_) as cf,n,prt) = findedge eid gr
    in
    let (newinps,nomore) = match (PortMap.find prt n.inputs) with
      Left cmap ->
        let k = ConnectionMap.find cf cmap
        in
        if k > 1 then
          (Left (ConnectionMap.add cf (k-1) cmap), false)
        else
          (Left (ConnectionMap.remove cf cmap), true)
    | Right cset ->
        (Right (ConnectionSet.remove cf cset), true)
    in
    let ntoutes =
      if nomore && (IdtMap.mem n.id gr.toutes) then
      	IdtSet.fold (fun srcid toutescurr ->
      		IdtMap.add srcid (IdtSet.remove eid (IdtMap.find srcid toutescurr)) toutescurr
      	) (connectionsources cmap) gr.toutes
      else gr.toutes
    in
    {
      tnodes = IdtMap.add n.id 
        {n with inputs = PortMap.add prt newinps n.inputs} gr.tnodes;
      tedges = (if nomore then IdtMap.remove eid gr.tedges else gr.tedges);
      toutes = ntoutes
    };;
    

  let addedge_withid ((ncmap,ncid) as ncf,nnid,nprt) gr =
    let hasedge = try
      ignore (findedge ncid gr);
      true
    with Not_found -> false
    in
    let gr' = if hasedge then remedge ncid gr else gr
    in
    let nn = findnode nnid gr'
    and addedid = ref ncid
    in
    let newinpsforport = try
      match (PortMap.find nprt nn.inputs) with
        Left cmap ->
          let k = ConnectionMap.finddef 0 ncf cmap
          in
          if k > 0 then
          begin
            let ((ocmap,ocid) as ocf) = match ConnectionMap.fold (fun ocf _ y ->
              match y with
                Some _ -> y
              | None -> if (ConnectionMap.comparekeys ocf ncf) = 0
                  then Some ocf else None
            ) cmap None with Some x -> x | None -> assert false
            in
            addedid := ocid;
            Left (ConnectionMap.add ocf (k+1) cmap)
          end
          else
            Left (ConnectionMap.add ncf 1 cmap)
      | Right cset ->
          if ConnectionSet.mem ncf cset then
          begin
            let (ocmap,ocid) as ocf = ConnectionSet.choose (
                ConnectionSet.filter (fun x ->
                  (ConnectionSet.comparekeys x ncf) = 0) cset)
            in
            addedid := ocid;
            Right cset
          end
          else
            Right (ConnectionSet.add ncf cset)
    with Not_found ->
    begin
      match (portdesc nprt).inputnum with
        PortBounded _ ->
          Left (ConnectionMap.add ncf 1 ConnectionMap.empty)
      | PortUnbounded -> 
          Right (ConnectionSet.singleton ncf)
    end
    in
    let nn' = {nn with inputs = PortMap.add nprt newinpsforport nn.inputs}
    in
    let ntnodes = IdtMap.add nn.id nn' gr'.tnodes
    in
    if !addedid <> ncid then
      ({gr' with tnodes = ntnodes}, !addedid)
    else
    let ntedges = IdtMap.add ncid (ncf,nn.id,nprt) gr'.tedges
    and ntoutes = IdtSet.fold (fun ncsourceid toutescurr ->
      let s = try 
        IdtMap.find ncsourceid toutescurr
      with Not_found -> IdtSet.empty
      in
      IdtMap.add ncsourceid (IdtSet.add ncid s) toutescurr
    ) (connectionsources ncmap) gr'.toutes
    in
    ({tnodes = ntnodes; tedges = ntedges; toutes = ntoutes}, ncid);;

  let addedge x gr =
    let (gr',_) = addedge_withid x gr
    in gr';;

  let nodefoldoutedges gr f n v0 =
    let outedges = try IdtMap.find n.id gr.toutes with Not_found -> IdtSet.empty
    in
    IdtSet.fold (fun eid im ->
      let (ec,nid,prt) = IdtMap.find eid gr.tedges
      in
      let nn = IdtMap.find nid gr.tnodes
      in
      f (ec,nn,prt) im
    ) outedges v0;;
  
  let nodefoldoutedges gr f n v0 =
    foldedges (fun ((ec,ecid),nn,prt) w ->
      if IdtSet.mem n.id (connectionsources ec) then f ((ec,ecid),nn,prt) w else w) gr v0;;

  let addnode n gr =
    let gr' = if hasnode n.id gr then remnode n.id gr else gr
    in
    let ntnodes = IdtMap.add n.id n gr'.tnodes
    and ntedges = nodefoldedges (fun ((ecmap,ecid) as ec,nn,prt) ->
      IdtMap.add ecid (ec,nn.id,prt) ) n gr'.tedges
    and ntoutes = nodefoldedges (fun ((ecmap, ecid),nn,prt) imm ->
    	IdtSet.fold (fun ecsourceid toutescurr ->
			let s = try IdtMap.find ecsourceid toutescurr with Not_found -> IdtSet.empty
		    in
            IdtMap.add ecsourceid (IdtSet.add ecid s) toutescurr
       	) (connectionsources ecmap) imm
      ) n gr'.toutes
    in {
      tnodes = ntnodes;
      tedges = ntedges;
      toutes = if IdtMap.mem n.id ntoutes then ntoutes else IdtMap.add n.id IdtSet.empty ntoutes
    };;
    
    let changenode n gr =
    	if not (hasnode n.id gr) then addnode n gr else
    	let nold = findnode n.id gr
    	in
    	if n.outputindextype <> nold.outputindextype then raise (Failure "DG.changenode") else
        let (tedges',toutes') = nodefoldedges (fun ((conn,eid),_,tgtport) (tedgescurr,toutescurr) ->
  	    	let tedgesnext = IdtMap.remove eid tedgescurr
  	    	and toutesnext = IdtSet.fold (fun csourceid ttt -> let ccss = IdtMap.find csourceid ttt in IdtMap.add csourceid (IdtSet.remove eid ccss) ttt) (connectionsources conn) toutescurr
  	    	in (tedgesnext, toutesnext)
  		) nold (gr.tedges, gr.toutes)
      	in
    	{
	        tnodes = IdtMap.add n.id n gr.tnodes;
    	    tedges = tedges';
    	    toutes = toutes';
        }
;;
  
(*
  let idsToNew gr =
    let o2n = Hashtbl.create 100
    in
    let newid x =
      try
        Hashtbl.find o2n x
      with Not_found ->
      begin
        let y = NewName.get ()
        in Hashtbl.add o2n x y;
        y
      end
    in
    let newedge cf =
      { sourceid = newid cf.sourceid;
        lblmap = cf.lblmap;
        nameforudg = newid cf.nameforudg }
    in
    foldnodes (fun n ->
      let nid' = newid n.id
      and inputs' = PortMap.map (function
        Left cmap -> Left (
          ConnectionMap.fold (fun cf x ->
            ConnectionMap.add (newedge cf) x
          ) cmap ConnectionMap.empty
        )
      | Right cset -> Right (ConnectionSet.map newedge cset)
      ) n.inputs
      in
      let n' = {n with id = nid'; inputs = inputs'}
      in
      addnode n'
    ) gr empty
*)

let edges_to_port gr nodeid prt =
	let n = findnode nodeid gr
	in
	nodefoldedges (fun ((_,eid),_,prt') s ->
		if prt = prt' then IdtSet.add eid s else s
	) n IdtSet.empty
;;

end :
sig
  type t
  
  val empty : t
  val addnode : nodetype -> t -> t
  val changenode : nodetype -> t -> t
  val hasnode : NewName.idtype -> t -> bool
  val findnode : NewName.idtype -> t -> nodetype
  val foldnodes : (nodetype -> 'a -> 'a) -> t -> 'a -> 'a
  val nodefoldedges : (connectiontype * nodetype * portname -> 'a -> 'a) -> nodetype -> 'a -> 'a
  val nodefoldoutedges : t -> (connectiontype * nodetype * portname -> 'a -> 'a) -> nodetype -> 'a -> 'a
  val foldedges : (connectiontype * nodetype * portname -> 'a -> 'a) -> t -> 'a -> 'a
  val foldedgesources : (NewName.idtype -> 'a -> 'a) -> connectiontype -> 'a -> 'a
  val remnode : NewName.idtype -> t -> t
  val findedge : NewName.idtype -> t -> connectiontype * nodetype * portname
  val remedge : NewName.idtype -> t -> t
  val addedge : (connectiontype * NewName.idtype * portname) -> t -> t
  val addedge_withid : (connectiontype * NewName.idtype * portname) -> t -> (t * NewName.idtype)
  val edges_to_port : t -> NewName.idtype -> portname -> IdtSet.t
  (*val idsToNew : t -> t*)
end);;

