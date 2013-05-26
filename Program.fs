let uncurry = fun f -> fun x -> fun y -> f (x, y)
let first = fun f -> fun (x, y) -> (f x, y)
let second = fun f -> fun (x, y) -> (x, f y)
let flip = fun f -> fun x -> fun y -> f y x
let ( *** ) f g = fun (x, y) -> (f x, g y)

open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core

type Element =
    | Val of int
    | Var of string
    override this.ToString() : string =
        match this with
        | Val x -> x.ToString()
        | Var x -> x

let mjoin s =
    ((fun x -> x.ToString()) |> Array.map)
    >> fun (xs : string[]) -> System.String.Join(s, xs)

type Monomial =
    | Prod of Element[]
    static member (*) (x, y) =
        match (x, y) with
        | (Prod e, Prod f) -> Prod((e |> Array.append) f)
    override this.ToString() =
        match this with
        | Prod xs -> if xs.Length = 0 then "1" else xs |> mjoin "*"

type Polynomial =
    | Sum of Monomial[]
    static member (+) (x, y) =
        match (x, y) with
        | (Sum e, Sum f) -> Sum((e |> Array.append) f)
    override this.ToString() : string =
        match this with
        | Sum xs -> if xs.Length = 0 then "0" else xs |> mjoin "+"
    static member (*) (x, y) =
        match (x, y) with
        | (Sum xs, m) -> Sum(xs |> (flip (*) m |> Array.map)) 
    static member (*) (x, y) =
        match (x, y) with
        | (m, Sum xs) -> Sum(xs |> ((*) m |> Array.map))
    static member (*) (x, y : Polynomial) =
        match (x, y) with
        | (Sum xs, _) -> Sum(xs |> ((flip (*) y >> (fun p -> match p with Sum ms -> ms)) |> Array.map) |> Array.concat)

type Expression =
    | Elem of Element
    | Mono of Monomial
//    | Poly of Polynomial
    | Product of Expression[]
    | Sumation of Expression[]
    static member (+) (x, y) = Sumation [|x; y|]
    static member (*) (x, y) = Product [|x; y|]
    override this.ToString() =
        match this with
        | Elem x -> x.ToString()
        | Mono x -> x.ToString()
//        | Poly x -> "(" + x.ToString() + ")"
        | Product xs -> if xs.Length = 0 then "1" else xs |> mjoin "*"
        | Sumation xs -> if xs.Length = 0 then "0" else (if xs.Length = 1 then "" else "(") + (xs |> mjoin "+") + (if xs.Length = 1 then "" else ")")
    member this.parenthesize start count =
        match this with
        | Product xs -> Product (((
                                        xs.[..(start - 1)] |> Array.append)
                                        [|Product xs.[start..(start + count - 1)]|] |> Array.append)
                                        xs.[(start + count)..])
        | Sumation xs -> Sumation (((
                                        xs.[..(start - 1)] |> Array.append)
                                        [|Sumation xs.[start..(start + count - 1)]|] |> Array.append)
                                        xs.[(start + count)..])
        | _ -> this
    // (a+b+...)(c+d+...) -> a(c+d+...) + b(c+d+...) + ...
    member this.expand () =
        match this with
        | Product xs ->
            let x = Array.map (fun (x : Expression) -> x.expand ()) xs in
            if Array.fold (fun s -> fun p -> s || snd p) false x then // naibu de seikou
                (Product(Array.fold (fun s -> fun p -> Array.append s [|fst p|]) [||] x), true)
            elif x.Length <= 1 then
                (this, false)
            else // no low-level expand done.
                match xs.[0] with
                | Sumation ys ->
                    (Sumation (Array.map (fun (y : Expression) -> Product(Array.append [|y|] xs.[1..])) ys), true)
                | _ ->
                let pr = (Product xs.[1..]).expand() in
                    if snd pr then
                        (Product(Array.append [|xs.[0]|] [|(fst pr)|]), true)
                    else
                        match xs.[1] with
                        | Sumation ys ->
                            (Sumation (Array.map (fun (y : Expression) -> Product(Array.append [|xs.[0]; y|] xs.[2..])) ys), true)
                        | _ -> (this, false)
        | Sumation xs ->
            let x = Array.map (fun (x : Expression) -> x.expand ()) xs in
            if Array.fold (fun s -> fun p -> s || snd p) false x then
                (Sumation(Array.fold (fun s -> fun p -> Array.append s [|fst p|]) [||] x), true)
            else
                (this, false)
        | _ -> (this, false)

let (>**>) = fun f -> fun g -> Array.unzip >> (f *** g)
//let doublefold = fun f -> fun g -> fun a -> fun b -> (Array.fold f a) >**> (Array.fold g b)

let any = Array.fold (||) false
let concany = Array.concat >**> any

let toFlatProductList =
    Array.map (function
    | Product ys -> (ys, true)
    | y -> ([|y|], false)) >> concany

let toFlatSumationList : Expression[] -> (Expression[] * bool) =
    Array.map (function
    | Sumation ys -> (ys, true)
    | y -> ([|y|], false)) >> concany

let mapFlatten f g = Array.map f >> (g >**> any)
let oror = fun f -> fun ((x, y), z) -> (f x, y || z)

let rec flattenProduct : Expression -> Expression * bool = function
    | Sumation xs ->
        xs |> mapFlatten flattenProduct Sumation 
    | Product xs ->
        xs |> mapFlatten flattenProduct toFlatProductList |> oror Product
    | x -> (x, false)

let rec flattenSumation = function
    | Product xs ->
        xs |> mapFlatten flattenSumation Product
    | Sumation xs ->
        xs |> mapFlatten flattenSumation toFlatSumationList |> oror Sumation
    | x -> (x, false)

let Poly = function Sum xs -> Sumation(Array.map Mono xs)

let f =
    Sum [|
        Prod[|Var "x"; Var "x"|];
        Prod[|Val 2; Var "x"|];
        Prod[|Val 1|]|]
let g =
    Sum [|
        Prod[|Var "x"|];
        Prod[|Val 3|]|]
let printexpression name expression =
    System.Console.WriteLine("{0} = {1}", name, expression.ToString())
let rec printExpression name (expression : Expression) =
    System.Console.WriteLine("{0} = {1}", name, expression.ToString())
    let (x, f) = expression.expand () in
        if f then
            System.Console.Write("expanded ")
            printExpression name x
        else
            System.Console.Write("non-expanded ")
            let (y, g) = flattenSumation x in
                if g then
                    System.Console.Write("s-flattened ")
                    printExpression name y
                else
                    System.Console.Write("non-s-flattened ")
                    let (z, h) = flattenProduct y in
                        if h then
                            System.Console.Write("p-flattened ")
                            printExpression name z
                        else
                            System.Console.WriteLine("non-p-flattened ")


let main =
    printexpression "1" (Val 1)
    printexpression "f" f
    printexpression "g" g
    printexpression "f+g" (f + g)
    printexpression "f*g" (f * g)
    printExpression "f*g" (Product [|Poly f; Poly g|])
    printExpression "g*g*g" (Product [|Poly g; Poly g; Poly g|])

main

//type MonomiaL = Product of Element list
//type PolynomiaL = Sum of MonomiaL list
//
//let monomiaLToMonomial = function 
//    | Product x -> x |> (List.fold (uncurry Mul) EmptyProduct)
//let polynomiaLToPolynomial = function
//    | Sum x -> x |> (List.fold (uncurry (Add << second monomiaLToMonomial) ) EmptySum)
//let rec toMonomiaL = function
//    | EmptyProduct -> Product []
//    | Mul (m, e) -> (toMonomiaL m) |> function
//        | Product x -> (e :: x) |> List.sort |> Product
//let rec toPolynomiaL = function
//    | EmptySum -> Sum []
//    | Add (p, m) -> (toPolynomiaL p) |> function
//        | Sum x -> (toMonomiaL m :: x) |> List.sort |> Sum
//
//let rec eval = function
//    | Val x -> x
//    | Var x -> System.ArgumentOutOfRangeException("cannot evaluate formula with variables.") |> raise
//let rec evalua = function
//    | EmptyProduct -> 1
//    | Mul (m, e) -> (evalua m) + (eval e)
//let rec evaluate = function
//    | EmptySum -> 0
//    | Add (p, m) -> (evaluate p) + (evalua m)
//
//let rec substi x y = function
//    | Val z -> Val z
//    | Var z -> if x = z then Val y else Var z
//let rec substitu x y = function
//    | EmptyProduct -> EmptyProduct
//    | Mul (m, e) -> Mul (substitu x y m, substi x y e)
//let rec substitute x y = function
//    | EmptySum -> EmptySum
//    | Add (p, m) -> Add (substitute x y p, substitu x y m)

//let tost = function
//    | Val z -> z.ToString()
//    | Var z -> z
//let rec tostri = function
//    | EmptyProduct -> "1"
//    | Mul (EmptyProduct, e) -> tost e
//    | Mul (m, e) -> tostri m + "*" + tost e
//let rec tostring = function
//    | EmptySum -> "0"
//    | Add (EmptySum, m) -> tostri m
//    | Add (p, m) -> tostring p + " + " + tostri m

//let rec (+) = function
//    | EmptySum -> (id : Polynomial -> Polynomial)
//    | Add (p, m) -> function
//        | EmptySum -> Add (p, m)
//        | Add (p', m') -> Add (Add (p, m) + p', m')
//let rec mulpp : Polynomial -> Polynomial -> Polynomial = function
//    | EmptySum -> fun _ -> EmptySum
//    | Add (p, m) -> function
//        | EmptySum -> EmptySum
//        | Add (p', m') -> Add (mulpp p p' + mulpm p m' + mulmp m p', mulmm m m')
//and mulpm = function
//    | EmptySum -> fun _ -> EmptySum
//    | Add (p, m) -> function
//        | EmptyProduct -> Add (p, m)
//        | Mul (m', e') -> Add (mulpm p (Mul (m', e')), Mul (mulmm m m', e'))
//and mulmp = function
//    | EmptyProduct -> (id : Polynomial -> Polynomial)
//    | Mul (m, e) -> function
//        | EmptySum -> EmptySum
//        | Add (p', m') -> Add (mulmp (Mul (m, e)) p', mulmm (Mul (m, e)) m')
//and mulmm = function
//    | EmptyProduct -> (id : Monomial -> Monomial)
//    | Mul (m, e) -> function
//        | EmptyProduct -> Mul (m, e)
//        | Mul (m', e') -> Mul (mulmm (Mul (m, e)) m', e')


//type Expression =
//    | Add of Expression * Expression
//    | Mul of Expression * Expression
//    | Val of int
//    | Var of string
//
//let rec parenth = function
//    | Add (x, y) -> "(" + (tostring x) + " + " + (tostring y) + ")"
//    | x -> tostring x
//and tostring = function
//    | Add (x, y) -> (tostring x) + " + " + (tostring y)
//    | Mul (x, y) -> (parenth x) + "*" + (parenth y)
//    | Val x -> x.ToString()
//    | Var x -> x
//
//let rec substitute x y = function
//    | Add (l, r) -> Add (substitute x y l, substitute x y r)
//    | Mul (l, r) -> Mul (substitute x y l, substitute x y r)
//    | Val z -> Val z
//    | Var z -> if x = z then Val y else Var z
//
//let rec eval = function
//    | Add (l, r) -> (eval l) + (eval r)
//    | Mul (l, r) -> (eval l) * (eval r)
//    | Val z -> z
//    | Var z -> raise (System.ArgumentOutOfRangeException("cannot evaluate formula with variables."))
//
//let rec hasMulAdd = function
//    | Val z -> false
//    | Var z -> false
//    | Add (l, r) -> (hasMulAdd l) || (hasMulAdd r)
//    | Mul (Add (x, y), z) -> true
//    | Mul (x, Add (y, z)) -> true
//    | Mul (l, r) -> (hasMulAdd l) || (hasMulAdd r)
//
//let rec expand = function
//    | Add (l, r) -> Add (expand l, expand r)
//    | Val z -> Val z
//    | Var z -> Var z
//    | Mul (Val x, Val y) -> Val (x * y)
//    | Mul (Var x, Val y) -> Mul (Val y, Var x)
//    | Mul (Add (a, b), c) ->
//        if hasMulAdd a || hasMulAdd b || hasMulAdd c then
//            Mul (Add (expand a, expand b), expand c)
//        else
//            Add (Mul (a, c), Mul(b, c))
//    | Mul (a, Add (b, c)) ->
//        if hasMulAdd a || hasMulAdd b || hasMulAdd c then
//            Mul (expand a, Add (expand b, expand c))
//        else
//            Add (Mul (a, b), Mul(a, c))
//    | Mul (p, q) -> Mul (p, q)
//
////let rec deepexpand = function
////    | Mul (p, q) -> Mul (expand p, expand q)
////    | x -> expand x
//
//let isSimple = function
//    | Var z -> true
//    | Val z -> true
//    | _ -> false
//let rec isSumOfProduct = function
//    | Add (x, y) -> (isSumOfProduct x) && (isSumOfProduct y)
//    | Var z -> true
//    | Val z -> true
//    | Mul (x, y) -> (isSimple x) && (isSimple y)
//
//let printFormula name expression =
//    System.Console.WriteLine("{0} = {1}", name, tostring expression)
//
//let main =
//    let showexpands f0 =
//        printFormula "f0" f0
//        printFormula "f1" (f0 |> expand)
//        printFormula "f2" (f0 |> expand |> expand)
//        printFormula "f3" (f0 |> expand |> expand |> expand)
//        printFormula "f4" (f0 |> expand |> expand |> expand |> expand)
//        printFormula "f5" (f0 |> expand |> expand |> expand |> expand |> expand)
//    showexpands (Mul (Mul (Add (Var "x", Val 1), Add (Var "x", Val 2)), Add (Var "x", Val 3)))
//    showexpands (Mul (Add (Var "x", Val 1), Mul(Add (Var "x", Val 2), Add (Var "x", Val 3))))
//
//main
