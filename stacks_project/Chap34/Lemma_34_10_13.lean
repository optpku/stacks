module

import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Criteria
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 34.10.13: For a quasi-compact scheme morphism, the singleton `V`-covering
condition, valuation-ring extension lifting, and universal specialization lifting are
equivalent. -/
@[stacks 0ETN] #check
  (AlgebraicGeometry.isVCovering_singleton_tfae :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f],
      List.TFAE [
        AlgebraicGeometry.IsVCovering Y (fun _ : PUnit ↦ X) (fun _ ↦ f),
        AlgebraicGeometry.ValuationRingExtensionLift f,
        AlgebraicGeometry.UniversalSpecializationLift f])
