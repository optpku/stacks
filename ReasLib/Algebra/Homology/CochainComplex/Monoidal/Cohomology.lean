module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Differential
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MC

# Cohomology products induced by pairings of cochain complexes

A chain map out of a tensor complex has a canonical value on pairs of cocycles.  Descent from
cocycles to cohomology is recorded as a property of an explicit morphism: tensoring quotient maps
need not preserve epimorphisms in an arbitrary monoidal abelian category, so no choice or global
instance is introduced here.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open ComplexShape

noncomputable section

universe u v

namespace HomologicalComplex.CohomologyCup

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
variable [MonoidalPreadditive C]
variable {K L H : CochainComplex C ℤ} [HasTensor K L]

/-- The value of a chain-level pairing on cocycles has zero differential. -/
@[stacks 07MC "chain pairing sends pairs of cocycles to cocycles"]
theorem cycles_d (γ : tensorObj K L ⟶ H) (p q : ℤ) :
    ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫
          ιTensorObj K L p q (p + q) rfl) ≫ γ.f (p + q)) ≫
      H.d (p + q) (p + q + 1) = 0 := sorry

/-- Evaluate a chain-level pairing on two cocycles and pass to cohomology in the intrinsic
degree `p + q`. -/
@[stacks 07MC "chain pairing on cocycles"]
noncomputable def cycles (γ : tensorObj K L ⟶ H) (p q : ℤ)
    : K.cycles p ⊗ L.cycles q ⟶ H.homology (p + q) :=
  H.liftCycles
      ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫
        ιTensorObj K L p q (p + q) rfl) ≫ γ.f (p + q))
      (p + q + 1) (CochainComplex.next ℤ (p + q)) (cycles_d γ p q) ≫
    H.homologyπ (p + q)

/-- Transport the cocycle-level product to a displayed target degree `r`.  The degree equality is
explicit data, rather than being hidden in an existential or a local typeclass instance. -/
@[stacks 07MC "chain pairing on cocycles in a displayed degree"]
noncomputable def cyclesTo (γ : tensorObj K L ⟶ H) (p q r : ℤ)
    (h : p + q = r) :
    K.cycles p ⊗ L.cycles q ⟶ H.homology r :=
  match r, h with
  | _, rfl => cycles γ p q

/-- A cohomology morphism is induced by a chain-level pairing when precomposition with the two
cocycle quotient maps recovers the canonical cocycle-level product. -/
@[stacks 07MC "cohomology product induced by a chain pairing"]
def IsInduced (γ : tensorObj K L ⟶ H) (p q : ℤ)
    (cup : K.homology p ⊗ L.homology q ⟶ H.homology (p + q)) : Prop :=
  ((K.homologyπ p) ⊗ₘ (L.homologyπ q)) ≫ cup = cycles γ p q

/-- Displayed-degree form of `IsInduced`, with the target degree identification kept explicit. -/
@[stacks 07MC "cohomology product induced in a displayed degree"]
def IsInducedTo (γ : tensorObj K L ⟶ H) (p q r : ℤ)
    (h : p + q = r)
    (cup : K.homology p ⊗ L.homology q ⟶ H.homology r) : Prop :=
  ((K.homologyπ p) ⊗ₘ (L.homologyπ q)) ≫ cup = cyclesTo γ p q r h

/-- In the intrinsic target degree, the displayed-degree predicate is the ordinary induced-product
predicate. -/
@[stacks 07MC "intrinsic-degree induced cohomology product"]
theorem isInducedTo_rfl (γ : tensorObj K L ⟶ H) (p q : ℤ)
    (cup : K.homology p ⊗ L.homology q ⟶ H.homology (p + q)) :
    IsInducedTo γ p q (p + q) rfl cup ↔ IsInduced γ p q cup := sorry

end HomologicalComplex.CohomologyCup

end
