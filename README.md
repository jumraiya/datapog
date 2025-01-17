# Datapog

Toy datalog engine, mainly for learning purposes. There are mainly two relevant namespaces for now `datapog.parser` and `datapog.engine`.
	The former parses a datalog program (follows syntax similar to souffle), the latter calculates new facts until a fixed point is reached.

# Usage
```
lein run [datalog-file]
```

Or
```
lein repl
```

```
(require '[datapog.parser :refer [parse-program]])
(require '[datapog.engine :as engine])

;; Calculates transitive closure (reachability b/w nodes) of a graph
(-> ".decl edge(x: symbol, y:symbol)
    edge(a,b). edge(b,c). edge(c,d).
    tc(x,y) :- edge(x,y).
    tc(x,y) :- edge(x,z), tc(z,y)."
 (engine/validate+compile-program)
 (engine/semi-naive-eval)
 :facts)
```


# Goals
- Allow execution of datalog programs with recursion and negation

- Use fixed point semantics and semi-naive evaluation

- Implement pushdown automata for chain queries, magic sets rewriting

# TODO
- Implement disjunctions

- Implement pushdown automata for chain queries, magic sets rewriting
