/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
iff.rfl

example : (P ↔ Q) → (Q ↔ P) :=
iff.symm

example : (P ↔ Q) ↔ (Q ↔ P) :=
iff.comm

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
iff.trans

example : P ∧ Q ↔ Q ∧ P :=
and.comm

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
and.assoc

example : P ↔ (P ∧ true) :=
(and_true P).symm

example : false ↔ (P ∧ false) :=
(and_false P).symm

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
iff.and

example : ¬ (P ↔ ¬ P) :=
λ h, let x := h.mpr (λ x, h.mp x x) in h.mp x x
