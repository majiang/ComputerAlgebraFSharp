﻿let uncurry = fun f -> fun x -> fun y -> f (x, y)
let first = fun f -> fun (x, y) -> (f x, y)
let second = fun f -> fun (x, y) -> (x, f y)
let flip = fun f -> fun x -> fun y -> f y x
let ( *** ) f g = fun (x, y) -> (f x, g y)
let (++) = Array.append

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
        | (Prod e, Prod f) -> (e ++ f) |> Prod
    override this.ToString() =
        match this with
        | Prod xs -> if xs.Length = 0 then "1" else xs |> mjoin "*"

type Polynomial =
    | Sum of Monomial[]
    static member (+) (x, y) =
        match (x, y) with
        | (Sum e, Sum f) -> (e ++ f) |> Sum
    override this.ToString() : string =
        match this with
        | Sum xs -> if xs.Length = 0 then "0" else xs |> mjoin "+"
    member this.unSum =
        match this with
        | Sum ts -> ts
    static member (*) ((x : Polynomial), (y : Monomial)) =
        x.unSum |> (flip (*) y |> Array.map) |> Sum 
    static member (*) ((x : Monomial), (y : Polynomial)) =
        y.unSum |> ((*) x |> Array.map) |> Sum
    static member (*) (x : Polynomial, y : Polynomial) =
        x.unSum |> ((flip (*) y >> (fun (p : Polynomial) -> p.unSum)) |> Array.map) |> Array.concat |> Sum

type Expression =
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
        | Sumation xs -> if xs.Length = 0 then "0" else (if xs.Length = 1 then "" else "(") + (xs |> mjoin "+") + (if xs.Length = 1 then "" else ")")
    member this.parenthesize start count =
        match this with
        | Product xs -> (xs.[..(start - 1)] ++ [|Product xs.[start..(start + count - 1)]|] ++ xs.[(start + count)..]) |> Product
        | Sumation xs -> (xs.[..(start - 1)] ++ [|Sumation xs.[start..(start + count - 1)]|]  ++ xs.[(start + count)..]) |> Sumation
        | _ -> this

let rec expand = fun this ->
    match this with
        | Product xs ->
            let x = Array.map expand xs in
            if Array.fold (fun s -> fun p -> s || snd p) false x then // naibu de seikou
                (Product(Array.fold (fun s -> fun p -> Array.append s [|fst p|]) [||] x), true)
            elif x.Length <= 1 then
                (this, false)
            else // no low-level expand done.
                match xs.[0] with
                | Sumation ys ->
                    (Sumation (Array.map (fun (y : Expression) -> Product(Array.append [|y|] xs.[1..])) ys), true)
                | _ ->
                let pr = expand (Product xs.[1..]) in
                    if snd pr then
                        (Product(Array.append [|xs.[0]|] [|(fst pr)|]), true)
                    else
                        match xs.[1] with
                        | Sumation ys ->
                            (Sumation (Array.map (fun (y : Expression) -> Product(Array.append [|xs.[0]; y|] xs.[2..])) ys), true)
                        | _ -> (this, false)
        | Sumation xs ->
            let x = Array.map expand xs in
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
    let (x, f) = expand expression in
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
