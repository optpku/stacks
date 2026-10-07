module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import stacks_project.Chap62.Example_62_5_4_AssociatedCycle
public import stacks_project.Chap62.Lemma_62_4_1_Specialization

/-!
# Lemma 62.4.2

Specialization of cycles of a closed subscheme flat over a discrete valuation
ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The degree-`r` cycle of the inverse image of a closed subscheme in the
scheme-theoretic fibre over `s`. -/
noncomputable def fiberClosedSubschemeCycle {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (Z : X.IdealSheafData) (s : S) (r : ℕ)
    (h : topologicalKrullDim (f.fiberClosedSubscheme Z s).subscheme ≤
      (r : WithBot ℕ∞)) :
    CycleGroup (f.fiber s) (f.fiberDimensionFunction s) r :=
  (f.fiberToSpecResidueField s).closedSubschemeCycle (fun _ ↦ (0 : ℤ))
    (f.fiberClosedSubscheme Z s) (r : ℤ)
    (f.fiberClosedSubschemeDeltaDimension_le_of_topologicalKrullDim_le Z r h)

/-- The fibre closed-subscheme cycle is the closed-subscheme cycle of the inverse
image of `Z` in `X_s`. -/
theorem fiberClosedSubschemeCycle_spec {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (Z : X.IdealSheafData) (s : S) (r : ℕ)
    (h : topologicalKrullDim (f.fiberClosedSubscheme Z s).subscheme ≤
      (r : WithBot ℕ∞)) :
    fiberClosedSubschemeCycle f Z s r h =
      (f.fiberToSpecResidueField s).closedSubschemeCycle (fun _ ↦ (0 : ℤ))
        (f.fiberClosedSubscheme Z s) (r : ℤ)
        (f.fiberClosedSubschemeDeltaDimension_le_of_topologicalKrullDim_le Z r h) :=
  sorry

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
variable (W : X.IdealSheafData) (r : ℕ)

/-- Lemma 62.4.2 (1): if `R` is a discrete valuation ring, `X` is locally of finite type
over `R`, and `W ⊂ X` is a closed subscheme flat over `R` whose generic fibre has
dimension at most `r`, then the special fibre of `W` has dimension at most `r`. -/
@[stacks 0H4J]
theorem topologicalKrullDim_fiberClosedSubscheme_specialFiber_le
    (hflat : Flat (W.subschemeι ≫ f))
    (hK : topologicalKrullDim
      (f.fiberClosedSubscheme W
        (genericPoint (Spec (CommRingCat.of R)))).subscheme ≤
      (r : WithBot ℕ∞)) :
    topologicalKrullDim
      (f.fiberClosedSubscheme W (IsLocalRing.closedPoint R)).subscheme ≤
      (r : WithBot ℕ∞) :=
  sorry

/-- Lemma 62.4.2 (2): under the same hypotheses, the specialization map
`cycleSpecialization` sends the degree-`r` cycle of `W` on the generic fibre to
the degree-`r` cycle of `W` on the special fibre. -/
@[stacks 0H4J]
theorem cycleSpecialization_closedSubscheme
    (hflat : Flat (W.subschemeι ≫ f))
    (hK : topologicalKrullDim
      (f.fiberClosedSubscheme W
        (genericPoint (Spec (CommRingCat.of R)))).subscheme ≤
      (r : WithBot ℕ∞)) :
    f.cycleSpecialization r
      (f.fiberClosedSubschemeCycle W
        (genericPoint (Spec (CommRingCat.of R))) r hK) =
      f.fiberClosedSubschemeCycle W (IsLocalRing.closedPoint R) r
        (f.topologicalKrullDim_fiberClosedSubscheme_specialFiber_le W r hflat hK) :=
  sorry

end AlgebraicGeometry.Scheme.Hom
