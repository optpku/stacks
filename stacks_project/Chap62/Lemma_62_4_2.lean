module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization.ClosedSubscheme
import StacksCheckRecall

/-!
# Lemma 62.4.2

Specialization of cycles of a closed subscheme flat over a discrete valuation
ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/- Lemma 62.4.2 (1): a flat closed subscheme's generic-fibre dimension bound
also bounds its special-fibre dimension. -/
@[stacks 0H4J] #check
  (AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_fiberClosedSubscheme_specialFiber_le :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
      (W : X.IdealSheafData) (r : ℕ)
      (hflat : Flat (W.subschemeι ≫ f))
      (hK : topologicalKrullDim
        (f.fiberClosedSubscheme W
          (genericPoint (Spec (CommRingCat.of R)))).subscheme ≤ (r : WithBot ℕ∞)),
      topologicalKrullDim
        (f.fiberClosedSubscheme W (IsLocalRing.closedPoint R)).subscheme ≤
        (r : WithBot ℕ∞))

/- Lemma 62.4.2 (2): specialization identifies the generic and special
degree-`r` cycles of a flat closed subscheme. -/
@[stacks 0H4J] #check
  (AlgebraicGeometry.Scheme.Hom.cycleSpecialization_closedSubscheme :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
      (W : X.IdealSheafData) (r : ℕ)
      (hflat : Flat (W.subschemeι ≫ f))
      (hK : topologicalKrullDim
        (f.fiberClosedSubscheme W
          (genericPoint (Spec (CommRingCat.of R)))).subscheme ≤ (r : WithBot ℕ∞)),
      f.cycleSpecialization r
        (f.fiberClosedSubschemeCycle W
          (genericPoint (Spec (CommRingCat.of R))) r hK) =
        f.fiberClosedSubschemeCycle W (IsLocalRing.closedPoint R) r
          (f.topologicalKrullDim_fiberClosedSubscheme_specialFiber_le W r hflat hK))
