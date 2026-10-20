module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.CanonicalSource
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.KFlat
open Scheme.ModuleDerived.CompactSupport
open scoped DerivedCategory.CohomologyIn

universe u

/- Lemma 48.33.1: canonical compact-support duality over a field, normalized
by the structure sheaf under upper shriek. The actual horizontal isomorphism
is functorial in the bounded coherent complex and preserves the weak dual
and compact-support inverse-limit topologies. -/
@[stacks 0G5A]
#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.canonicalSourceDuality :
  {k : Type u} → [Field k] →
  (U : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k))) →
  [HomotopyTensorDescends (dualityCompactification U).obj.right.left.toRingedSpace] →
  [TensorDescends (dualityCompactification U).obj.right.left.toRingedSpace] →
  [IsLocalization (dualityCompactification U).obj.right.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived (dualityCompactification U).obj.right.left.toRingedSpace)] →
  [HomotopyTensorDescends U.obj.left.toRingedSpace] →
  [TensorDescends U.obj.left.toRingedSpace] → [IsLocalization U.obj.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived U.obj.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has
    (C := RingedSpace.Modules (dualityCompactification U).obj.right.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has (C := (dualityCompactification U).obj.right.left.Modules)] →
  (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) → (d : ℤ) →
    Module.Dual k ((Scheme.ModuleDerived.Cohomology.globalCohomologyOverField U.obj.hom d).obj K.obj.obj) ≃ₗ[k]
      cohomology (dualityCompactification U).obj.right.hom
        (Scheme.ModuleDerived.DeligneSystem.boundedTower
          (Scheme.Compactification.Of.ι (dualityCompactification U))
          (Scheme.ModuleDerived.DeligneSystem.extension
            (Scheme.Compactification.Of.ι (dualityCompactification U))
            (normalizedSourceDual (dualityCompactification U).obj.right.hom
              (Scheme.Compactification.Of.ι (dualityCompactification U)) K))) (-d))

#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.canonicalSourceDuality_topology :
  {k : Type u} → [Field k] →
  (U : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k))) →
  [HomotopyTensorDescends (dualityCompactification U).obj.right.left.toRingedSpace] →
  [TensorDescends (dualityCompactification U).obj.right.left.toRingedSpace] →
  [IsLocalization (dualityCompactification U).obj.right.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived (dualityCompactification U).obj.right.left.toRingedSpace)] →
  [HomotopyTensorDescends U.obj.left.toRingedSpace] →
  [TensorDescends U.obj.left.toRingedSpace] → [IsLocalization U.obj.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived U.obj.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has
    (C := RingedSpace.Modules (dualityCompactification U).obj.right.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has (C := (dualityCompactification U).obj.right.left.Modules)] →
  (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) → (d : ℤ) →
    cohomologyTopology (dualityCompactification U).obj.right.hom
        (Scheme.ModuleDerived.DeligneSystem.boundedTower
          (Scheme.Compactification.Of.ι (dualityCompactification U))
          (Scheme.ModuleDerived.DeligneSystem.extension
            (Scheme.Compactification.Of.ι (dualityCompactification U))
            (normalizedSourceDual (dualityCompactification U).obj.right.hom
              (Scheme.Compactification.Of.ι (dualityCompactification U)) K))) (-d) =
      TopologicalSpace.induced (canonicalSourceDuality U K d).symm
        (FiniteDual.topology k
          ((Scheme.ModuleDerived.Cohomology.globalCohomologyOverField U.obj.hom d).obj K.obj.obj)))

#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.canonicalSourceDuality_naturality :
  {k : Type u} → [Field k] →
  (U : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k))) →
  [HomotopyTensorDescends (dualityCompactification U).obj.right.left.toRingedSpace] →
  [TensorDescends (dualityCompactification U).obj.right.left.toRingedSpace] →
  [IsLocalization (dualityCompactification U).obj.right.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived (dualityCompactification U).obj.right.left.toRingedSpace)] →
  [HomotopyTensorDescends U.obj.left.toRingedSpace] →
  [TensorDescends U.obj.left.toRingedSpace] → [IsLocalization U.obj.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived U.obj.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has
    (C := RingedSpace.Modules (dualityCompactification U).obj.right.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has (C := (dualityCompactification U).obj.right.left.Modules)] →
  {K L : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]} → (a : K ⟶ L) → (d : ℤ) →
    (canonicalSourceDuality U K d).toLinearMap.comp
        ((Scheme.ModuleDerived.Cohomology.globalCohomologyOverField U.obj.hom d).map
          ((DerivedCategory.Bounded.CohomologyIn.ambient
            (SheafOfModules.isCoherent U.obj.left.ringCatSheaf)).map a)).hom.dualMap =
      (canonicalSourceCompactMap U a (-d)).hom.comp
        (canonicalSourceDuality U L d).toLinearMap)
