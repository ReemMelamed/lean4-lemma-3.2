import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Basic
import Mathlib.Tactic


section definitions

variable {S α : Type*} [Semigroup S] [LinearOrder α]

structure MultiplicativeLabelling (S α : Type*) [Semigroup S] [LinearOrder α] where
  σ : α → α → S
  prop : ∀ x y z : α, x < y → y < z → σ x y * σ y z = σ x z

def Split (α : Type*) (h : ℕ) := α → Fin h

variable {h : ℕ}

def Split.Equiv (s : Split α h) (x y : α) : Prop :=
  s x = s y ∧ ∀ z, min x y ≤ z → z ≤ max x y → s z ≤ s x

def IsRamsey (L : MultiplicativeLabelling S α) (s : Split α h) : Prop :=
  ∀ x y : α, x < y → Split.Equiv s x y → ∃ e : S, e * e = e ∧ L.σ x y = e

def IsNormalized [Fintype α] [Nonempty α] (s : Split α h) : Prop :=
  let min_a := Finset.min' Finset.univ Finset.univ_nonempty
  (s min_a : ℕ) = h - 1

end definitions


section theorems

variable {G α : Type*} [Group G] [Fintype G] [DecidableEq G]

variable [LinearOrder α] [Fintype α] [Nonempty α]

variable {h : ℕ}

theorem Split.is_equivalence (s : Split α h) : Equivalence (Split.Equiv s) := by
  sorry

instance : NeZero (Fintype.card G) := NeZero.of_pos (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩)

theorem simon_group_case (σ : MultiplicativeLabelling G α) :
    ∃ (s : Split α (Fintype.card G)), IsNormalized s ∧ IsRamsey σ s := by
  sorry

end theorems
