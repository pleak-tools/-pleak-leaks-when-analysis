
type ('a,'b) either = Left of 'a | Right of 'b ;;

let eithercomp leftcomp rightcomp a b =
  match a,b with
    Left x, Left y -> leftcomp x y
  | Left _, Right _ -> -1
  | Right _, Left _ -> 1
  | Right x, Right y -> rightcomp x y;;

let const k x = k;;

let id x = x;;

let curry f x y = f (x,y);;

let uncurry f (x,y) = f x y;;

let flip f x y = f y x;;

let cfun f x a y = if x = y then a else f y;;

let (>>=) v f = match v with
|	None -> None
|	Some x -> f x;;

let xor x y = if x then not y else y;;

exception NotSuitable;;

exception Successful;;

let rec intersperse l x = match l with
  [] -> []
| [y] -> [y]
| (y::ys) -> y :: x :: (intersperse ys x);;

let string_of_list soe l = List.fold_right (fun x -> (^) (soe x)) l "";;

let rec intfromto m n =
  if m > n then [] else m :: (intfromto (m+1) n);;

let rec listcompare cf l1 l2 = match l1,l2 with
  [],[] -> 0
| [],_ -> -1
| _,[] -> 1
| (x::xs), (y::ys) -> let p1 = cf x y 
                    in if p1 <> 0 then p1 else listcompare cf xs ys;;

let lexiccompare cf1 cf2 (x1,x2) (y1,y2) =
  let r1 = cf1 x1 y1
  in if r1 <> 0 then r1 else cf2 x2 y2;;

let rec iterate compfun f x =
  let y = f x
  in if (compfun x y) = 0 then x
  else iterate compfun f y;;

let rec listcartesian l1 l2 = match l1 with
  [] -> []
| (x::xs) -> (List.map (fun y -> (x,y)) l2) @ (listcartesian xs l2);;

let rec subsetlist l = match l with
  [] -> [[]]
| y :: ys -> let z = subsetlist ys in
  List.append z (List.map (fun a -> y :: a) z);;

let rec funcpow n f = if n=0 then id else fun x -> (funcpow (n-1) f) (f x);;

let rec makeProducts xla = 
	List.fold_right (fun a0 xx ->
		Array.fold_right (fun a acc -> (List.map (fun y -> a :: y) xx) @ acc) a0 []
	) xla [[]];;

