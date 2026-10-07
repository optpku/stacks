module

public import Mathlib.Order.JordanHolder
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Abelian.FiniteLength
public import ReasLib.CategoryTheory.Subobject.Quotient

/-!
# Jordan-Hölder Theory for Abelian Categories

The subobject lattice of an object in an abelian category carries a canonical
`JordanHolderLattice` structure.  Covers are ordinary lattice covers and the factor attached to
`X ≤ Y` is the canonical subquotient `Y / X`.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace Subobject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/-- A comparable pair `X ≤ Y` is a cover exactly when the canonical subquotient `Y / X` is
simple. -/
theorem covBy_iff_simple_subobjectSubquotient {X Y : Subobject A} (hXY : X ≤ Y) :
    X ⋖ Y ↔ Simple (subobjectSubquotient hXY) := sorry

/-- The second isomorphism theorem for canonical subquotients. -/
theorem subquotientSecondIso (X Y : Subobject A) :
    Nonempty
      (subobjectSubquotient (_root_.le_sup_left : X ≤ X ⊔ Y) ≅
        subobjectSubquotient (_root_.inf_le_right : X ⊓ Y ≤ Y)) := sorry

/-- The canonical Jordan-Hölder lattice structure on `Subobject A`, with factors represented by
canonical subquotients. -/
noncomputable instance instJordanHolderLattice : JordanHolderLattice (Subobject A) where
  IsMaximal := fun X Y ↦ X ⋖ Y
  lt_of_isMaximal := sorry
  sup_eq_of_isMaximal := sorry
  isMaximal_inf_left_of_isMaximal_sup := sorry
  Iso X Y := Nonempty
    (subobjectSubquotient (_root_.inf_le_right : X.1 ⊓ X.2 ≤ X.2) ≅
      subobjectSubquotient (_root_.inf_le_right : Y.1 ⊓ Y.2 ≤ Y.2))
  iso_symm := sorry
  iso_trans := sorry
  second_iso := sorry

/-- For comparable pairs, the Jordan-Hölder `Iso` relation is exactly isomorphism of the
corresponding canonical subquotients. -/
theorem iso_iff_nonempty_subobjectSubquotient_iso {X₁ X₂ Y₁ Y₂ : Subobject A}
    (hX : X₁ ≤ X₂) (hY : Y₁ ≤ Y₂) :
    JordanHolderLattice.Iso (X₁, X₂) (Y₁, Y₂) ↔
      Nonempty (subobjectSubquotient hX ≅ subobjectSubquotient hY) := sorry

end Subobject

end CategoryTheory

namespace CompositionSeries

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/-- The canonical subquotient attached to the `i`-th step of a composition series of
subobjects. -/
@[stacks 0FCK "composition-series factor object"]
noncomputable abbrev factor
    (s : CompositionSeries (Subobject A)) (i : Fin s.length) : C :=
  subobjectSubquotient (s.step i).le

/-- Every canonical factor of a composition series of subobjects is simple. -/
@[stacks 0FCK "simple composition-series factor"]
theorem factorSimple (s : CompositionSeries (Subobject A)) (i : Fin s.length) :
    Simple (s.factor i) := sorry

/-- Factorwise Jordan-Hölder for two composition series with the same endpoints. -/
theorem jordanHolderFactorsOfEndpoints
    (F G : CompositionSeries (Subobject A))
    (hhead : F.head = G.head) (hlast : F.last = G.last) :
    ∃ σ : Fin F.length ≃ Fin G.length,
      ∀ i : Fin F.length, Nonempty (F.factor i ≅ G.factor (σ i)) := sorry

/-- Lemma 12.9.7 (Tag 0FCK): two composition series from `0` to an object have isomorphic
factors up to a permutation. -/
@[stacks 0FCK]
theorem jordanHolderFactors
    (F G : CompositionSeries (Subobject A))
    (hF₀ : F.head = ⊥) (hF₁ : F.last = ⊤)
    (hG₀ : G.head = ⊥) (hG₁ : G.last = ⊤) :
    ∃ σ : Fin F.length ≃ Fin G.length,
      ∀ i : Fin F.length, Nonempty (F.factor i ≅ G.factor (σ i)) := sorry

end CompositionSeries

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A finite-length object admits a composition series from the zero subobject to the whole
object. -/
theorem existsCompositionSeries (A : C) [IsFiniteLengthObject A] :
    ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := sorry

/-- Lemma 12.9.6 (Tag 0FCJ), in its canonical formulation: finite length is equivalent to the
existence of a composition series of subobjects from `0` to the whole object.  Combined with
`isFiniteLengthObject_iff`, this is the source statement in terms of Artinian and Noetherian
objects. -/
@[stacks 0FCJ]
theorem isFiniteLengthObject_iff_existsCompositionSeries (A : C) :
    IsFiniteLengthObject A ↔
      ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := sorry

end CategoryTheory
