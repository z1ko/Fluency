# Fluency
An interpreter, type-checker and pretty-printer for a simple language, written in SML. 

## Usage
To execute arbitrary commands in the interactive enviroment use the following:
```
mosml store.sml eval.sml
```

Four structures of functions are defined:
- **ExprInt**: simple interpreter for the language, it evaluates expressions into the smallest normal form.
- **TypeChecker**: does type-checking on an expression and returns the infered type if possible.
- **PrettyPrinter**: prints expressions in human readable form.
- **Store**: Facilitate the manipulation of the store and the gamma sets.

## Language
The interpreted toy language has the following grammar (only relevant parts are shown):
```
e ::= n                         // Integer
    | b                         // Boolean
    | e op e                    // Op
    | if e then e else e        // If
    | e; e                      // Seq
    | while e do e              // While
    | skip                      // Skip
    | loc := e                  // Assign
    | !e                        // Deref
    | e || e                    // Parallel
    | await e protect e end     // Await (Mutex)
    | e Y e                     // Non Det. Choice
    ;
```
with standard typing and **small-step CBV** semantic rules.
