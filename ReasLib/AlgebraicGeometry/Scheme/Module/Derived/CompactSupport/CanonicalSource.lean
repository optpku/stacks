/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.SourceRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.CompactificationChange

@[expose] public section
open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.KFlat
open scoped DerivedCategory.CohomologyIn
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
variable {k : Type u} [Field k]

/-- A compactification supplied by the existing Nagata owner for the finite-type
separated structure morphism. Only this genuine geometric existence choice is made. -/
def dualityCompactification (U : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k))) :
    Scheme.Compactification.Of (Spec (CommRingCat.of k)) U.obj :=
  Classical.choice (Scheme.Compactification.Of.instNonempty
    (Scheme.FiniteTypeSeparatedOver.toBase U))

/-- The chosen compactification's interior is over the original field base. -/
theorem dualityCompactification_fac
    (U : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k))) :
    Scheme.Compactification.Of.ι (dualityCompactification U) ≫
      (dualityCompactification U).obj.right.hom = U.obj.hom :=
  (dualityCompactification U).obj.hom.w

variable (U U' : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
variable [HomotopyTensorDescends (dualityCompactification U).obj.right.left.toRingedSpace]
variable [TensorDescends (dualityCompactification U).obj.right.left.toRingedSpace]
variable [IsLocalization (dualityCompactification U).obj.right.left.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived
  (dualityCompactification U).obj.right.left.toRingedSpace)]
variable [HomotopyTensorDescends U.obj.left.toRingedSpace]
variable [TensorDescends U.obj.left.toRingedSpace] [IsLocalization U.obj.left.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived U.obj.left.toRingedSpace)]
variable [HomotopyTensorDescends U'.obj.left.toRingedSpace]
variable [TensorDescends U'.obj.left.toRingedSpace] [IsLocalization U'.obj.left.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived U'.obj.left.toRingedSpace)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has
  (C := RingedSpace.Modules (dualityCompactification U).obj.right.left.toRingedSpace)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has
  (C := (dualityCompactification U).obj.right.left.Modules)]

/-- The common compactification also factors the smaller open's original
structure morphism, using that f is a morphism over the field. -/
theorem canonicalRestrictedBase (f : U' ⟶ U) :
    (f.hom.left ≫ Scheme.Compactification.Of.ι (dualityCompactification U)) ≫
      (dualityCompactification U).obj.right.hom = U'.obj.hom := sorry

/-- Canonical normalized duality on a finite-type separated source, using
the chosen compactification and the ideal of the existing Deligne extension. -/
def canonicalSourceDuality
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :=
  let P := dualityCompactification U
  let j := Scheme.Compactification.Of.ι P
  let S := DeligneSystem.extension j K
  let e := eqToIso (congrArg
    (fun p ↦ (Cohomology.globalCohomologyOverField p d).obj K.obj.obj)
    (dualityCompactification_fac U))
  e.toLinearEquiv.dualMap.trans
    (sourceDuality P.obj.right.hom j K S.ideal S.openComplement_eq d)

/-- The canonical normalized horizontal is a topological linear isomorphism
for the source's weak dual topology and actual compact-support limit topology. -/
theorem canonicalSourceDuality_topology
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    cohomologyTopology (dualityCompactification U).obj.right.hom
        (DeligneSystem.boundedTower (Scheme.Compactification.Of.ι (dualityCompactification U))
          (DeligneSystem.extension (Scheme.Compactification.Of.ι (dualityCompactification U))
            (normalizedSourceDual (dualityCompactification U).obj.right.hom
              (Scheme.Compactification.Of.ι (dualityCompactification U)) K))) (-d) =
      TopologicalSpace.induced (canonicalSourceDuality U K d).symm
        (FiniteDual.topology k ((Cohomology.globalCohomologyOverField U.obj.hom d).obj K.obj.obj)) := sorry

/-- The contravariant map of literal source duals is RHom precomposition,
lifted through the fully faithful bounded-coherent inclusion. -/
def canonicalSourceDualMap
    {K L : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]} (a : K ⟶ L) :
    normalizedSourceDual (dualityCompactification U).obj.right.hom
        (Scheme.Compactification.Of.ι (dualityCompactification U)) L ⟶
      normalizedSourceDual (dualityCompactification U).obj.right.hom
        (Scheme.Compactification.Of.ι (dualityCompactification U)) K :=
  (DerivedCategory.Bounded.CohomologyIn.ambient
    (SheafOfModules.isCoherent U.obj.left.ringCatSheaf)).preimage
      ((CategoryTheory.MonoidalClosed.pre
        ((DerivedCategory.Bounded.CohomologyIn.ambient
          (SheafOfModules.isCoherent U.obj.left.ringCatSheaf)).map a)).app
            (openDualizing (dualityCompactification U).obj.right.hom
              (Scheme.Compactification.Of.ι (dualityCompactification U))))

/-- Compact cohomology acts on the actual contravariant source-dual map. -/
def canonicalSourceCompactMap
    {K L : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]} (a : K ⟶ L) (d : ℤ) :=
  Pro.ModuleLimit.map (Cohomology.overFieldFunctor (dualityCompactification U).obj.right.hom d)
    ((DeligneSystem.extensionByZero
      (Scheme.Compactification.Of.ι (dualityCompactification U))).map (canonicalSourceDualMap U a))

/-- The canonical normalized topological duality is functorial in the
bounded coherent input, for the specified ordinary and compact coefficient maps. -/
theorem canonicalSourceDuality_naturality
    {K L : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]} (a : K ⟶ L) (d : ℤ) :
    (canonicalSourceDuality U K d).toLinearMap.comp
        ((Cohomology.globalCohomologyOverField U.obj.hom d).map
          ((DerivedCategory.Bounded.CohomologyIn.ambient
            (SheafOfModules.isCoherent U.obj.left.ringCatSheaf)).map a)).hom.dualMap =
      (canonicalSourceCompactMap U a (-d)).hom.comp
        (canonicalSourceDuality U L d).toLinearMap := sorry

/-- The smaller open uses the same proper compactification and its actual
restricted input, with the Deligne owner's prescribed ideal. -/
def canonicalRestrictedSourceDuality (f : U' ⟶ U) [IsOpenImmersion f.hom.left]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :=
  let P := dualityCompactification U
  let j := Scheme.Compactification.Of.ι P
  let j' := f.hom.left ≫ j
  let K' := (DeligneSystem.restriction f.hom.left).obj K
  let S' := DeligneSystem.extension j' K'
  let e := eqToIso (congrArg
    (fun p ↦ (Cohomology.globalCohomologyOverField p d).obj K'.obj.obj)
    (canonicalRestrictedBase U U' f))
  e.toLinearEquiv.dualMap.trans
    (sourceDuality P.obj.right.hom j' K' S'.ideal S'.openComplement_eq d)

/-- The ordinary restriction between original sources, before taking the
contragredient, uses the specified base-factorization isomorphism. -/
def canonicalSourceOrdinaryRestriction (f : U' ⟶ U) [IsOpenImmersion f.hom.left]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :=
  let P := dualityCompactification U
  let j := Scheme.Compactification.Of.ι P
  let e := eqToIso (congrArg
    (fun p ↦ (Cohomology.globalCohomologyOverField p d).obj K.obj.obj)
    (dualityCompactification_fac U))
  let e' := eqToIso (congrArg
    (fun p ↦ (Cohomology.globalCohomologyOverField p d).obj
      ((DeligneSystem.restriction f.hom.left).obj K).obj.obj)
    (canonicalRestrictedBase U U' f))
  e.inv ≫ normalizedOrdinaryRestriction P.obj.right.hom j f.hom.left K d ≫ e'.hom

/-- The compact vertical map is realization of the canonical open restriction
on the normalized dual, in the same proper compactification. -/
def canonicalSourceCompactRestriction (f : U' ⟶ U) [IsOpenImmersion f.hom.left]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :=
  normalizedCompactRestriction (dualityCompactification U).obj.right.hom
    (Scheme.Compactification.Of.ι (dualityCompactification U)) f.hom.left K d

/-- The canonical square has no compactification, ideal, extension,
comparison map or compatibility law supplied by the caller. -/
theorem canonicalSourceDuality_commonCompactificationRestriction
    (f : U' ⟶ U) [IsOpenImmersion f.hom.left]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    (canonicalSourceCompactRestriction U U' f K (-d)).hom.comp
        (canonicalRestrictedSourceDuality U U' f K d).toLinearMap =
      (canonicalSourceDuality U K d).toLinearMap.comp
        (canonicalSourceOrdinaryRestriction U U' f K d).hom.dualMap := sorry

variable [HomotopyTensorDescends (dualityCompactification U').obj.right.left.toRingedSpace]
variable [TensorDescends (dualityCompactification U').obj.right.left.toRingedSpace]
variable [IsLocalization (dualityCompactification U').obj.right.left.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived
  (dualityCompactification U').obj.right.left.toRingedSpace)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has
  (C := RingedSpace.Modules (dualityCompactification U').obj.right.left.toRingedSpace)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has
  (C := (dualityCompactification U').obj.right.left.Modules)]

/-- The smaller open's compact endpoint changes from the parent's model to
its independently chosen canonical model by the actual geometric transport. -/
def canonicalRestrictedCompactificationIso (f : U' ⟶ U) [IsOpenImmersion f.hom.left]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :=
  normalizedCompactificationIso U'
    (restrictedCompactification U U' f (dualityCompactification U))
    (dualityCompactification U') ((DeligneSystem.restriction f.hom.left).obj K) d

/-- The actual compactification-change map intertwines the normalized
trace-derived horizontal with the same canonical horizontal used for U'. -/
theorem canonicalRestrictedSourceDuality_change
    (f : U' ⟶ U) [IsOpenImmersion f.hom.left]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    (canonicalRestrictedCompactificationIso U U' f K (-d)).hom.hom.comp
        (canonicalRestrictedSourceDuality U U' f K d).toLinearMap =
      (canonicalSourceDuality U' ((DeligneSystem.restriction f.hom.left).obj K) d).toLinearMap := sorry

/-- Compact restriction between independent canonical compact-support
endpoints transports by the actual common-refinement map before geometric restriction. -/
def canonicalIndependentCompactRestriction
    (f : U' ⟶ U) [IsOpenImmersion f.hom.left]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :=
  (canonicalRestrictedCompactificationIso U U' f K d).inv ≫
    canonicalSourceCompactRestriction U U' f K d

/-- The independent-endpoint restriction agrees with the geometric common-
compactification restriction under the specified change of compactification. -/
theorem canonicalIndependentCompactRestriction_change
    (f : U' ⟶ U) [IsOpenImmersion f.hom.left]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    (canonicalRestrictedCompactificationIso U U' f K d).hom ≫
        canonicalIndependentCompactRestriction U U' f K d =
      canonicalSourceCompactRestriction U U' f K d := sorry

/-- The source square uses the same canonical normalized horizontal on each
scheme, with actual geometric compactification change incorporated in the
right vertical map. No change-of-compactification compatibility is assumed. -/
theorem canonicalSourceDuality_openRestriction
    (f : U' ⟶ U) [IsOpenImmersion f.hom.left]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    (canonicalIndependentCompactRestriction U U' f K (-d)).hom.comp
        (canonicalSourceDuality U' ((DeligneSystem.restriction f.hom.left).obj K) d).toLinearMap =
      (canonicalSourceDuality U K d).toLinearMap.comp
        (canonicalSourceOrdinaryRestriction U U' f K d).hom.dualMap := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
