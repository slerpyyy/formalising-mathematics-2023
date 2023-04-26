/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : true :=
⟨⟩

example : true → true :=
id

example : false → true :=
false.elim

example : false → false :=
id

example : (true → false) → false :=
λ f, f ⟨⟩

example : false → P :=
false.elim

example : true → false → true → false → true → false :=
λ _ x _ _ _, x

example : P → ((P → false) → false) :=
λ x f, f x

example : (P → false) → P → Q :=
λ f x, (f x).elim

example : (true → false) → P :=
λ f, (f ⟨⟩).elim
