module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization

/-!
# Specialization of cycles of flat closed subschemes

The associated cycle of a closed subscheme flat over a discrete valuation ring
specializes from the generic fibre to the special fibre.
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
        (f.fiberClosedSubschemeDeltaDimension_le_of_topologicalKrullDim_le Z r h) := sorry

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
variable (W : X.IdealSheafData) (r : ℕ)

/-- A closed subscheme flat over a discrete valuation ring, inside a scheme locally
of finite type over that ring, has special-fibre dimension at most `r` whenever
its generic-fibre dimension is at most `r`. -/
theorem topologicalKrullDim_fiberClosedSubscheme_specialFiber_le
    (hflat : Flat (W.subschemeι ≫ f))
    (hK : topologicalKrullDim
      (f.fiberClosedSubscheme W
        (genericPoint (Spec (CommRingCat.of R)))).subscheme ≤
      (r : WithBot ℕ∞)) :
    topologicalKrullDim
      (f.fiberClosedSubscheme W (IsLocalRing.closedPoint R)).subscheme ≤
      (r : WithBot ℕ∞) := sorry

/-- Specialization sends the degree-`r` generic-fibre cycle of a closed subscheme
flat over a discrete valuation ring to its degree-`r` special-fibre cycle when
the generic-fibre dimension is at most `r`. -/
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
        (f.topologicalKrullDim_fiberClosedSubscheme_specialFiber_le W r hflat hK) := sorry

end AlgebraicGeometry.Scheme.Hom
