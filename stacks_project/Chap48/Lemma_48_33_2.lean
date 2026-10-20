module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.CanonicalSource
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.KFlat
open Scheme.ModuleDerived.CompactSupport
open scoped DerivedCategory.CohomologyIn

universe u

/- Lemma 48.33.2: compact-support duality commutes with open restriction.
Both horizontal maps are the same canonical normalized duality family of
Lemma 48.33.1, evaluated independently on each scheme. The right vertical
map includes the constructed proper-refinement transport of compact support
and the trace-normalized change of dualizing object. -/
@[stacks 0G5B]
#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.canonicalSourceDuality_openRestriction :
  {k : Type u} → [Field k] →
  (U U' : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k))) →
  [HomotopyTensorDescends (dualityCompactification U).obj.right.left.toRingedSpace] →
  [TensorDescends (dualityCompactification U).obj.right.left.toRingedSpace] →
  [IsLocalization (dualityCompactification U).obj.right.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived (dualityCompactification U).obj.right.left.toRingedSpace)] →
  [HomotopyTensorDescends U.obj.left.toRingedSpace] →
  [TensorDescends U.obj.left.toRingedSpace] → [IsLocalization U.obj.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived U.obj.left.toRingedSpace)] →
  [HomotopyTensorDescends U'.obj.left.toRingedSpace] →
  [TensorDescends U'.obj.left.toRingedSpace] → [IsLocalization U'.obj.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived U'.obj.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has
    (C := RingedSpace.Modules (dualityCompactification U).obj.right.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has (C := (dualityCompactification U).obj.right.left.Modules)] →
  [HomotopyTensorDescends (dualityCompactification U').obj.right.left.toRingedSpace] →
  [TensorDescends (dualityCompactification U').obj.right.left.toRingedSpace] →
  [IsLocalization (dualityCompactification U').obj.right.left.toRingedSpace] →
  [MonoidalClosed (RingedSpace.ModuleDerived (dualityCompactification U').obj.right.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has
    (C := RingedSpace.Modules (dualityCompactification U').obj.right.left.toRingedSpace)] →
  [DerivedCategory.DerivedTensor.Bifunctor.Has (C := (dualityCompactification U').obj.right.left.Modules)] →
  (f : U' ⟶ U) → [IsOpenImmersion f.hom.left] →
  (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) → (d : ℤ) →
    (canonicalIndependentCompactRestriction U U' f K (-d)).hom.comp
        (canonicalSourceDuality U' ((Scheme.ModuleDerived.DeligneSystem.restriction f.hom.left).obj K) d).toLinearMap =
      (canonicalSourceDuality U K d).toLinearMap.comp
        (canonicalSourceOrdinaryRestriction U U' f K d).hom.dualMap)
