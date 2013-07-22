let curry = fun f -> fun x -> fun y -> (x, y) |> f
let uncurry = fun f -> fun (x, y) -> x |> f <| y
let diagonal = fun x -> (x, x)
let first = fun f -> fun (x, y) -> (f x, y)
let second = fun f -> fun (x, y) -> (x, f y)
let flip = fun f -> fun x -> fun y -> f y x
let ( *** ) = fun f -> fun g -> fun (x, y) -> (f x, g y)
let (<^|) = flip // f <^| b = fun a -> a |> f <| b
let ( <|> ) = fun x -> fun f -> x |> Array.map f
let (++) = Array.append // (a ++ b) == (a |> Array.append <| b)
let ifte<'T> : bool -> 'T * 'T -> 'T = function
    | true -> fst
    | false -> snd

open Microsoft.FSharp.Collections
open Microsoft.FSharp.Core


type Element = /// Type for element of an algebraic stracture.
    | Val of int
    | Var of string
    override this.ToString() : string =
        match this with
        | Val x -> x.ToString()
        | Var x -> x

let mjoin s = /// Join with separator an array using .ToString() call
    (Array.map (fun x -> x.ToString())) >> fun xs -> System.String.Join(s, xs)

type Monomial = /// Type for monomial.
    | Prod of Element[]
    member x.unProd = match x with Prod fs -> fs
    static member (*) (x : Monomial, y : Monomial) =
        (x.unProd ++ y.unProd) |> Prod
    override x.ToString() =
        x.unProd |> fun xs -> if xs.Length = 0 then "1" else xs |> mjoin "*"

type Polynomial = /// Type for Polynomial.
    | Sum of Monomial[]
    member x.unSum = match x with Sum ts -> ts
    static member (+) (x : Polynomial, y : Polynomial) =
        (x.unSum ++ y.unSum) |> Sum
    override x.ToString() : string =
        x.unSum |> fun xs -> if xs.Length = 0 then "0" else xs |> mjoin "+"
    static member (*) ((x : Polynomial), (y : Monomial)) =
        x.unSum <|> flip (*) y |> Sum
    static member (*) ((x : Monomial), (y : Polynomial)) =
        y.unSum <|> (*) x |> Sum
    static member (*) (x : Polynomial, y : Polynomial) =
        x.unSum <|> (flip (*) y >> (fun (p : Polynomial) -> p.unSum)) |> Array.concat |> Sum

let ifsp<'T> = fun (xs : 'T[]) -> fun p -> if xs.Length = 1 then "" else p

type Expression = /// Type for more general expression.
    | Elem of Element
    | Mono of Monomial
    | Product of Expression[]
    | Sumation of Expression[]
    static member (+) (x, y) = Sumation [|x; y|]
    static member (*) (x, y) = Product [|x; y|]
    override this.ToString() =
        match this with
        | Elem x -> x.ToString()
        | Mono x -> x.ToString()
        | Product xs -> if xs.Length = 0 then "1" else xs |> mjoin "*"
        | Sumation xs -> if xs.Length = 0 then "0" else (ifsp xs "(") + (xs |> mjoin "+") + (ifsp xs ")")

let unproduct this =
    match this with
    | Product xs -> xs

type IsChanged<'T> =
    | Changed of 'T
    | Unchanged of 'T
let forgetIsChanged<'T> : IsChanged<'T> -> 'T = function
    | Changed x -> x
    | Unchanged x -> x
let getIsChanged = function
    | Changed _ -> true
    | Unchanged _ -> false
let mapForget<'T> =
    Array.map forgetIsChanged<'T>
let choose f g =
    getIsChanged >> (flip ifte (f, g))
let chooseChanged<'U, 'T> : IsChanged<'U>[] -> 'T -> IsChanged<'T> =
    Array.exists getIsChanged >> flip ifte (Changed, Unchanged)
let chooseWith f g =
    diagonal >> (forgetIsChanged *** choose f g) >> (uncurry (|>))
let chooseWithAfter h f g =
    chooseWith (h >> f) (h >> g)

// やりたいこと:
// - 展開などにおいて「expandC を map して一か所でも Changed なら Changed にくるむ、さもなければ自分自身を展開」
// - expandC を試して Changed ならそのまま返す、さもなければ他の関数を試す
//type IsChangedBuilder() =
//    member __.Bind(isch, expr) =
//        expr (forgetIsChanged isch)
//    member __.Return(x) =
//        Unchanged x
//    member __.Delay(f) =

let isAnywhereChanged<'U> : IsChanged<'U>[] -> IsChanged<'U[]> =
    diagonal >> (mapForget *** chooseChanged<'U, 'U[]>) >> (uncurry (|>))

let split<'T> start count = fun (xs : 'T[]) -> (xs.[..(start - 1)], xs.[start..(start+count-1)], xs.[(start + count)..])
let inner f = fun (x, y, z) -> (x ++ [|f y|] ++ z)

type ParenthesisPosition =
    | Last of int * int
    | Deeper of int * ParenthesisPosition

let parenthesize = fun start -> fun count -> function
    | Product xs -> xs |> split start count |> inner Product |> Product
    | Sumation xs -> xs |> split start count |> inner Sumation |> Sumation
    | x -> x

let rec parenthesizeDeeper = function
    | Last (start, count) -> parenthesize start count
    | Deeper (i, p) -> function
        | Product xs -> xs |> split i 1 |> inner (fun x -> x.[0] |> parenthesizeDeeper p) |> Product
        | Sumation xs -> xs |> split i 1 |> inner (fun x -> x.[0] |> parenthesizeDeeper p) |> Sumation
        | x -> x

let foo = Product >> Changed

let rec expandCF : Expression[] -> IsChanged<Expression> =
    fun xs -> match xs.Length with
    | 0 -> xs |> Product |> Unchanged
    | 1 -> xs.[0] |> Changed
    | _ ->
        match xs.[0] with
        | Sumation ys -> // 先頭が和なら展開
            ys |> 
            (((fun y -> Array.append [|y|] xs.[1..]) >> Product) |> Array.map) |>
            Sumation |> Changed
        | other -> // 先頭は和ではないので、後ろの部分を展開 (できないこともある)
            xs.[1..] |> Product |> expandC |> chooseWithAfter
                (fun ys -> [|other; ys|] |> Product) Changed Unchanged // Unchanged の場合、末尾の展開を試す必要あり。ただしこれは異なる戦略としておく方がよいかも。
and expandC : Expression -> IsChanged<Expression> = function
    | Product xs ->
        xs <|> expandC |> isAnywhereChanged |> chooseWith (Product >> Changed) expandCF
    | Sumation xs ->
        xs <|> expandC |> isAnywhereChanged |> chooseWithAfter Sumation Changed Unchanged
    | other -> other |> Unchanged



//let (>**>) = fun f -> fun g -> Array.unzip >> (f *** g)
//let doublefold = fun f -> fun g -> fun a -> fun b -> (Array.fold f a) >**> (Array.fold g b)

//let any = Array.fold (||) false
//let concany = Array.concat >**> any


// concany : [C<[T]>] -> C<[T]>
let concany =
    isAnywhereChanged >> // C<[[T]]>
    chooseWithAfter Array.concat Changed Unchanged

let toFlatProducts =
    Array.map (function
    | Product ys -> ys |> Changed
    | y -> Unchanged [|y|]) >> concany

let toFlatSumations =
    Array.map (function
    | Sumation ys -> ys |> Changed
    | y -> Unchanged [|y|]) >> concany

//let mapFlatten f g = Array.map f >> (g >**> any)
//let oror = fun f -> fun ((x, y), z) -> (f x, y || z)

//let rec joinWith = fun flatten -> (function
//    | Sumation xs -> xs |> flatten |> chooseWithAfter Sumation Changed Unchanged
//    | Product xs -> xs |> flatten |> chooseWithAfter Product Changed Unchanged
//    | other -> other |> Unchanged)
let rec joinProduct = function
    | Product xs -> xs |> toFlatProducts |> chooseWithAfter Product Changed Unchanged
    | Sumation xs -> xs <|> joinProduct |> isAnywhereChanged |> chooseWithAfter Sumation Changed Unchanged
    | other -> other |> Unchanged
let rec joinSumation = function
    | Sumation xs -> xs |> toFlatSumations |> chooseWithAfter Sumation Changed Unchanged
    | Product xs -> xs <|> joinSumation |> isAnywhereChanged |> chooseWithAfter Product Changed Unchanged
    | other -> other |> Unchanged

let Poly = function Sum xs -> xs <|> Mono |> Sumation

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
    expression
let rec printExpression name (expression : Expression) =
    let expanded = expression |> (printexpression name) |> expandC
    let pflattened = expanded |> chooseWithAfter (printexpression name) joinProduct joinProduct
    pflattened |> chooseWithAfter (printexpression name) joinSumation joinSumation
    
let main =
    //printexpression "1" (Val 1)
    //printexpression "f" f
    ignore (printexpression "g" g)
    //printexpression "f+g" (f + g)
    //printexpression "f*g" (f * g)
    //printExpression "f*g" (Product [|Poly f; Poly g|])
    let p = (printExpression "g*g*g") >> forgetIsChanged
    [|Poly g; Poly g; Poly g|] |> Product |> p |> p |> p |> p |> ignore
    System.Console.ReadLine() |> ignore

main |> ignore
