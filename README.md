# Morpheus
A Refinement Typed Parser Combinator DSL.


# Dependencies:
1. OCaml (Version >= 4.03)
2. Z3 
3. OCamlLex 

# To build:
```
./build.sh path-to-testfile.ml
```
This generates a testfile.native in the root directory

# To run:
./testfile.native path-to-testfile.spec 

# Example
```
./build.sh tests/unit/unit1.ml 
../unit1.native tests/unit/unit1.spec 

```

# Structure
- Type/Specification Language : ./speclang/specLang.ml
- Program/Term Language       : ./synlang/lambdasyn.ml 
- Typing Rules 	              : ./typechecking/syntypechecker.ml
- Tests 		              : ./tests/unit/
- Verification Conditions     : ./typechecking/verificationC.ml
- VCtoZ3 Encoding 	      : ./vcencode/vcencode.ml





