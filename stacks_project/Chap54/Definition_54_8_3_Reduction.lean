/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.ReductionPossible

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Compatibility checks for the reduction-possible API owned by ReasLib. -/
#check (@AlgebraicGeometry.Scheme.Hom.structureSheafH1Length :
  {A : Type u} → [CommRing A] → {X : Scheme.{u}} →
    (X ⟶ Spec (.of A)) → ℕ∞)
#check (@AlgebraicGeometry.Scheme.Hom.structureSheafH1Length_def :
  {A : Type u} → [CommRing A] → {X : Scheme.{u}} →
    (f : X ⟶ Spec (.of A)) →
      AlgebraicGeometry.Scheme.Hom.structureSheafH1Length f =
        Module.length A
          (AlgebraicGeometry.Scheme.Hom.cohomology f
            (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1))
#check (@RationalSingularity.ReductionPossible :
  (A : Type u) → [CommRing A] → Prop)
#check (@RationalSingularity.ReductionPossible.instIsLocalRing :
  (A : Type u) → [CommRing A] →
    [RationalSingularity.ReductionPossible A] → IsLocalRing A)
#check (@RationalSingularity.ReductionPossible.instNagataRing :
  (A : Type u) → [CommRing A] →
    [RationalSingularity.ReductionPossible A] → NagataRing A)
#check (@RationalSingularity.ReductionPossible.instIsNormalRing :
  (A : Type u) → [CommRing A] →
    [RationalSingularity.ReductionPossible A] → IsNormalRing A)
#check (@RationalSingularity.reductionPossible_iff :
  (A : Type u) → [CommRing A] →
    RationalSingularity.ReductionPossible A ↔
      IsLocalRing A ∧ NagataRing A ∧ IsNormalRing A ∧ ringKrullDim A = 2 ∧
        ∃ n : ℕ, ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsModification f],
          X.isNormal →
            AlgebraicGeometry.Scheme.Hom.structureSheafH1Length f ≤ (n : ℕ∞))
