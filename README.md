## Morpheus
A Refinement Typed Parser Combinator DSL.


## Dependencies:
1. OCaml (Version >= 4.03)
2. Z3 
3. OCamlLex 

## To build:
```
cd <project-root>
./build.sh <path-to-testfile>/testfile.native
```
This generates a testfile.native in the <project-root>/outputs directory

## To run:
```
./outputs/testfile.native <path-to-testfile>/testfile.spec 
```
## Example
```
./build.sh tests/unit/unit1.native 
./outputs/unit1.native tests/unit/unit1.spec 

```

## Directory Structure
- Type/Specification Language : <project-root>/speclang/specLang.ml
- Program/Term Language       : <project-root>/synlang/lambdasyn.ml 
- Typing Rules 	              : <project-root>/typechecking/syntypechecker.ml
- Unit and other tests 		  : <project-root>/tests/unit/
- Morpheus benchmarks         : <project-root>/benchmarks/safeparse/<benchmakr> 
- Verification Conditions     : <project-root>/typechecking/verificationC.ml
- VCtoZ3 Encoding 	          : <project-root>/vcencode/vcencode.ml





