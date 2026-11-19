---
"everystate": patch
---

A function from strings prints as a record only when every key is a name, as in TLC: `[k \in {"72", "dup:72"} |-> 1]` now prints as `("72" :> 1 @@ "dup:72" :> 1)` instead of `["72" |-> 1, "dup:72" |-> 1]`, which is not TLA+ and which tools that read TLC's output, such as the pstack `statechart` skill, could not parse. A key is a name, as TLC decides it, when it has a letter, only letters, digits and `_`, and does not start a fairness name such as `WF_x`.
