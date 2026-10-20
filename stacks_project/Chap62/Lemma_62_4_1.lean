module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Specialization
import StacksCheckRecall

/-!
# Lemma 62.4.1

Specialization of associated cycles of a coherent module flat over a discrete
valuation ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
variable (F : X.Modules) [F.IsCoherent] (r : ℕ)

/- Lemma 62.4.1 (1): the generic-fibre support dimension bound implies the
special-fibre support dimension bound. -/
@[stacks 0H4I] #check
  (AlgebraicGeometry.Scheme.Modules.topologicalKrullDim_moduleSupport_specialFiber_le f F r :
    (∀ x : X, Module.FlatAlong (f.stalkMap x).hom (RingedSpace.stalkModuleCat F x)) →
      fiberSupportDimension f F
          (genericPoint (Spec (CommRingCat.of R))) ≤ (r : WithBot ℕ∞) →
        fiberSupportDimension f F (IsLocalRing.closedPoint R) ≤ (r : WithBot ℕ∞))

/- Lemma 62.4.1 (2): specialization identifies the generic and special
degree-`r` associated cycles. -/
@[stacks 0H4I] #check
  (AlgebraicGeometry.Scheme.Modules.cycleSpecialization_associatedCycle f F r :
    (∀ x : X, Module.FlatAlong (f.stalkMap x).hom (RingedSpace.stalkModuleCat F x)) →
      fiberSupportDimension f F
          (genericPoint (Spec (CommRingCat.of R))) ≤ (r : WithBot ℕ∞) →
        Hom.cycleSpecialization f r
            (fiberAssociatedCycle f F
              (genericPoint (Spec (CommRingCat.of R))) r) =
          fiberAssociatedCycle f F (IsLocalRing.closedPoint R) r)

end AlgebraicGeometry.Scheme.Modules
