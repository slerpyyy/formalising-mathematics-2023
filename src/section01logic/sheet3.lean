/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
λ f, f ⟨⟩

example : false → ¬ true :=
λ x _, x

example : ¬ false → true :=
λ _, ⟨⟩

example : true → ¬ false :=
λ _ x, x

example : false → ¬ P :=
λ x _, x

example : P → ¬ P → false :=
λ x f, f x

example : P → ¬ (¬ P) :=
λ x f, f x

example : (P → Q) → (¬ Q → ¬ P) :=
λ f g, g∘f

example : ¬ ¬ false → false :=
λ f, f id

example : ¬ ¬ P → P :=
by_contra

example : (¬ Q → ¬ P) → (P → Q) :=
λ f x, by_contra (λ y, (f y) x)
