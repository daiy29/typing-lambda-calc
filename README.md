### Overview

There is one scala file focused on a representation of simply-typed λ-calculus.

### Scala Code

Included at the top, is the given code for the STType used for STAbs.

![Scala code](https://gyazo.com/1bcfe72c09b884ba88830840711d1695.png)

### Part 1

The STTerm type consists of the relevent definitions of the λ-calculus ST.
The constructors are

- STVar
- STApp
- STAbs
- STZero
- STSuc
- STIsZero
- STTrue
- STFalse
- STTest

STZero, STTrue, and STFalse are declared as singleton classes. Due to it not being explicitly stated in the requirements, the overridden toString() methods may be incomplete or incorrect. There was no practical use of it other than possibly in testing.

### Part 2

![Second](https://gyazo.com/03f4da56b7a680d1a176ec41e0fb3e80.png)

The next portion requires that we typecheck our class of ST-calculus. The typecheck method will take an STTerm, and returns true if the represented term obeys the type rules of ST; otherwise, it returns false. We require a method to determine the type of a given expression in typecheck, so this method is defined as typeOf. The option wrapper is used for the output, as we can pattern match all the possible **valid** inputs to a type. Any incorrect input is simply returned as a None case. This part is simply a translation of the logic of ST-Calculus.
![Next](https://gyazo.com/0d84997ed417f506e57426755f7f0853.png)

Finally, the typecheck method uses the typeOf method to determine if the type is correct. If the environment is not properly mapped, then it is false, if it is properly mapped then it is true.

![Third](https://gyazo.com/06a45e493e4137cd85af5ac9a2d35dfe.png)

### Part 3

The last portion requires us to implement a method eraseTypes which translates elements of STTerm into elements of ULTerm. The translations are given as following:

- true = λ t → λ f → t
- false = λ t → λ f → f
- test = λ l → λ m → λ n → l m n
- zero = λ s → λ z → z
- suc = λ n → λ s → λ z → s (n s z)
- iszero = λ m → m (λ x → false) true

![Last](https://gyazo.com/69b292f9623f29bdcd5aabe5b9133ae1.png)

Similar to part 2, this is a direct translation of the properties listed above. The cases for STApp, STAbs, STTest were derived from those properties. We used pattern matching since the language and its translation is finite and we are able to derive the appropriate ULTerms from it.
