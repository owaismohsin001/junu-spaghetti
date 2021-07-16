# Junu Spaghetti
Junu spaghetti is a language aimed at typing spaghetti code, especially kind people write in JS, Python, and other dynamically typed programming languages because you often don't want to write robust highly scalable code but a one-off script but would still like a nice type system to avoid debugging those pesky runtime type errors. It attempts this by using union types, polymorphism, and structural typing. What follows is a workable overview of Junu Spaghetti.

## Base types, and variables
The language has all the expected base types of a high-level programming language, such as
```
let b = true
let n = 1
let s = "Hello"
```
You may have noticed the lack of type annotations, this is because Junu generally has local inference and therefore can infer the type of most local declarations. These are typed exactly the way you would expect them to be typed. Here are the results of typing
```
b: Bool
n: Int
s: String
```
## Functions
Functions in Junu are first-class(and closures are also supported) meaning they can be passed to other functions, assigned to variables returned from functions. Following is an example of a function in Junu.
```
addNums(a: Int, b: Int) => Int {
    return a+b
}
```
and it's typed as 
```
addNums: (Int, Int) -> Int
```
Now, Junu can infer the return type of functions that don't recurse, either by themselves or through mutual recursion, which this function does not so let's omit the return type and see if it works.
```
let addNums = (a: Int, b: Int) => {
    return a+b
}
```
As you might have noticed, we are using anonymous class functions here which is a common way of asking for type inference on return types in Junu. You may also consider omitting the curly braces if your function consists only of a single expression like the function discussed above.
```
let addNums = (a: Int, b: Int) => a+b
``` 
You may also want to forward declare functions if you plan to call them, in other functions before defining them. This is usually only used when mutual recursion comes into play, but our example here is not that.
```
f(Int) => Int
let g = (i: Int) => f(i)
f = (i: Int) => i+1
```
This will be typed as
```
f: (Int) -> Int
g: (Int) -> Int
```

## Structural Types
These types are compared exclusively by their structures since they have no name. Following is an example of such a type
```
let obj = {a: 1, b: 3, c: "Hello"}
```
This will be typed as
```
obj: {a: Int, b: Int, c: String}
```
and any object even if aliased can be assigned to this variable

## Type Unions
Type Unions are a form of subtyping which prefers composition over inheritance and is the heart and soul of this programming language. Unions here can be explicitly annotated, like this
```
let x: Int | String = 1
x = "Hello"
```
or inferred like such
```
let x = 1
x = "Hello"
```
both of which will be typed as 
```
x: (Int | String)
```
You must note that a union can only be passed to a function that is either polymorphic over them or expects exactly the unions that are sent to it, this is done to preserve the soundness of the type system. 

## Narrowing Unions
Given a type, `Int | String`, there are ways to operate on it that can give you a singular type, and the main approach of doing that is using if statements, like such
```
let f = (a: Int | String) => {
    if a is Int {
        println(a+2)
    } else {
        println("Hello " + a)
    }
    return {}
}
```
This, when invoked with like this `f("World")`, prints `Hello World` but when invoked like this `f(3)` prints `5`. As you might have noticed other than narrowing the type of `a` to `Int` in the first block, it narrowed down the type of the `else` block to `String` as well. This functions just as well with early returns too, for instance, the function above can be re-written as
```
let f = (a: Int | String) => {
    if a is Int {
        println(a+2)
        return {}
    }
    println("Hello " + a)
    return {}
}
```
and be typed just as well. There also exist other operators such as the infix operator `notis` which is the opposite of `is`, and the unary `not` operator which negates an expression.

## Named Types
Named types allow for generic recursive structures, they are much like a pattern in Haskell but they have a type. Here's the type they have. Here's an example of a named type, with the name `Pair`
```
newtype Pair(a{}, b{}) = (a, b)
```
which can be instantiated as
```
let pair = Pair(1, "Hello")
```
which will be typed as
```
pair: Pair(Int, String)
```
and they can obviously be passed as generics and thus be nested
```
let pair = Pair(1, Pair({}, "Hello"))
```
while being typed as
```
pair: Pair(Int, Pair({}, String))
```
For a recursive type, when you want to generalize over its length, you can simply specify all the type variables in order like `len` function below does.
```
len(xs: Nil | Ls(n{})) => Int {
    if xs is Nil { return 0 }
    return len(xs.res)+1
}

let xs = Ls("d", Ls("ddjn", Ls("ddjn", {})))
println(len(xs))
```
Here `xs` would be typed as
```
xs: Ls(String, Ls(String, ({} | Ls(String))))
```
but will be generalized to `Ls(String)` when sending to a function, this generalization persists if it's returned from a function that generalizes it. When unions are put inside named types like
```
newtype Tup(a{}, b{}) = (a, b)
let t = Tup(1, "Hello")
t = Tup(1, 1)
```
their inner variables are turned into unions if possible
```
Tup = Tup(a{}, b{}) = fromList [(a,a{}),(b,b{})]
t: Tup(Int, (Int | String))
```

## Type Aliases
Type aliasing is used to build recursive and mutually recursive structures, here's an example
```
type Person = {name: String, age: Int, male: Bool, pet: Pet, parent: Nil | Person}
```
And objects of this kind can be interpreted as `Person` type.
```
let st = {name: "John", age: 10, male: true, pet: {species: "Cat", name: "Tom", color: "White"}, parent: {}}
```
Although, its immediate inferred type will be
```
st: {age: Int, male: Bool, name: String, parent: {}, pet: {color: String, name: String, species: String}}
```
but it can be sent to functions that accept `Person` type, like such
```
let st = {name: "John", age: 10, male: true, pet: {species: "Cat", name: "Tom", color: "White"}, parent: {}}
let mutatePerson = (s: Person, name: String) => {
    s.name = name
    return {}
}
mutatePerson(s, "Josh")
```
which is accepted to be sound. Even if we alter the type like this
```
st.parent = duplicate(st)
```
before sending it, as long as it's coercible to `Person`, it remains acceptable.

## Parametric polymorphism and constraints
Here we will show how generics and parametric polymorphism works in this language. Following is an example of an `identity` function that can take any type and return that type.
```
let identity = (a: x{}) => a
```
Here, this is typed simply as
```
identity: (x{}) -> x{}
```
where `x{}` can literally be any type, and a value of the same type will be returned because it's inferred as `(x{}) -> x{}`. The empty curly braces denote that there are no constraints on what this type can be. Here are a few examples of its invocations.
```
let n = identity(1)
let s = identity("Hello")
```
Since functions are first-class, they can be passed to `identity` as well, like this 
```
let f = identity((p: Int) => p+1)
```
All of which will be typed as 
```
f: (Int) -> Int
n: Int
s: String
```
Polymorphic functions can also constraint the values they are be willing to take, for example, we can define a function that can take `x`, if and only if `x` has a field called `name` of type `String`. What follows is an example,
```
let getName = (obj: x{.name: String}) => obj.name
```
Here are examples of what its invocations can be
```
let resA = getName({name: "Ameer"})
let resB = getName({name: "John", age: 20})
```
It is important to note that this is not structural subtyping, since this function
```
let idName = (obj: x{.name: String}) => obj
```
when invoked like such `let resB = idName({name: "John", age: 20})` would be typed as `{age: Int, name: String}`.
Note: Row polymorphism along is planned although it's not yet implemented.

## Arrays
Arrays in Junu are encoded entirely in its type system with the only aid coming from the language at runtime. This demonstrates the power of the system's union types quite effectively. You may initialize an array by either using the `Array` constructor or by using `insert` on an empty object. Here's an example of how type-safe heterogeneous arrays can be used in this language.
```
let insert = (arr: Nil | Array(m{}), a: n{}) => concat(arr, Array(a))
let res = insert(insert(insert({}, 1), true), "mooo")
res = concat(res, Array({p: true}))
```
An empty array can is to be represented as type `Nil`. This array can be indexed with the `index` function and it should return a type that's the union of all types present in the array. The union can then be narrowed with if statements. Following is an example of how this can be used 
```
if res notis Nil {
    let x = index(res, 3)
    if x is String {
        println(x + "hoo")
    } else if x is Int {
        println(x+1)
    } else {
        println(x)
    }
}
```

## Open functions
Open functions are the ad-hoc polymorphism of Junu. Open functions have many instantiations but those instantiations have to conform to the interface set by open functions, and can only be invoked with types that they are already instantiated with. Here's an example

```
open setName(t{}, String, a{.pet: b{.name: t{}}}) => b{.name: t{}} for a{.pet: b{.name: t{}}}

impl setName(s: String, area: String, person: Person) => {
    person.name = s
    return person.pet
} for Person

impl setName(i: Int, area: String, intkeeper: {pet: {name: Int}}) => {
    intkeeper.pet.name = i
    return intkeeper.pet
} for {pet: {name: Int}}
```

Now, this open function can only be called with either `{pet: {name: Int}}` or `Person`. Now let's call them with available
```
setName("Junu", "Collatz", {pet: {name: 1}})
```
