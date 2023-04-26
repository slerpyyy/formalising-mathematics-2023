/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
or.inl

example : Q → P ∨ Q :=
or.inr

example : P ∨ Q → (P → R) → (Q → R) → R :=
or.elim

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
or.swap
--or.rec or.inr or.inl

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
or.assoc
--⟨or.rec (or.rec (or.inl) (or.inr ∘ or.inl)) (or.inr ∘ or.inr),
--  or.rec (or.inl ∘ or.inl) (or.rec (or.inl ∘ or.inr) or.inr)⟩

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
or.imp
--λ f g, or.rec (or.inl ∘ f) (or.inr ∘ g)

example : (P → Q) → P ∨ R → Q ∨ R :=
or.imp_left
--λ f, or.rec (or.inl ∘ f) (or.inr)

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
iff.or
--λ f g, ⟨or.imp f.mp g.mp, or.imp f.mpr g.mpr⟩

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
--not_or_distrib
⟨λ h, ⟨h ∘ or.inl, h ∘ or.inr⟩, λ ⟨x, y⟩ h, h.elim x y⟩

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
--not_and_distrib
⟨λ f, by_contra (λ g, g (or.inl (λ x, g (or.inr (λ y, f ⟨x, y⟩))))),
  λ h, h.elim (λ f x, f x.1) (λ f x, f x.2)⟩
