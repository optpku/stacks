module

public import ReasLib.Algebra.Homology.DerivedCategory.Resolution.Exact
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization.KInjective
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Hom-complex cohomology after localized restriction

This leaf is the ringed-site specialization of the generic exact-functor comparison in
`CochainComplex.Resolution`.  Extension by zero supplies the exact left adjoint to restriction,
so an ambient K-injective target remains K-injective after localization automatically.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open RingedSite.Hom

noncomputable section

universe u v w z

namespace RingedSite.Hom.LocalizedRestriction.Homology

variable (X : RingedSite.{u, v, w}) (U : X) [UnivLE.{max u v, z}]
variable [SheafOfModules.Localization.HasLowerShriek.{z} X.structureSheaf]

/-- The degree-`n` Hom-complex cohomology of a restricted K-injective target computes shifted
morphisms in the localized derived category. -/
@[stacks 0CS5 "localized restriction Hom-complex degree-n equivalence"]
noncomputable def degreeAddEquiv
    (L I : CochainComplex (ModuleCat.{z} X) ℤ)
    [I.IsKInjective] (n : ℤ) :
    (CochainComplex.HomComplex
      ((localizedRestrictionComplex.{z} X U).obj L)
      ((localizedRestrictionComplex.{z} X U).obj I)).homology n ≃+
        ((localizedRestrictionDerived.{z} X U).obj (DerivedCategory.Q.obj L) ⟶
          ((localizedRestrictionDerived.{z} X U).obj (DerivedCategory.Q.obj I))⟦n⟧) :=
  @CochainComplex.Resolution.mapHomologyAddEquiv
    (ModuleCat.{z} X) inferInstance inferInstance (moduleCat_hasDerivedCategory X)
    (ModuleCat.{z} (X.localization U)) inferInstance (localizedModuleCatAbelian U)
      (localizedModuleCatHasDerivedCategory U)
    (localizedRestriction.{z} X U) (localizedRestriction_additive X U)
      (localizedRestriction_preservesFiniteLimits X U)
      (localizedRestriction_preservesFiniteColimits X U)
    L I (localizedRestrictionComplex_isKInjective X U I) n

/-- The degree-zero Hom-complex cohomology of a restricted K-injective target computes morphisms in
the localized derived category. -/
@[stacks 0A94 "localized restriction Hom-complex degree-zero equivalence"]
noncomputable def zeroAddEquiv
    (L I : CochainComplex (ModuleCat.{z} X) ℤ)
    [I.IsKInjective] :
    (CochainComplex.HomComplex
      ((localizedRestrictionComplex.{z} X U).obj L)
      ((localizedRestrictionComplex.{z} X U).obj I)).homology (0 : ℤ) ≃+
        ((localizedRestrictionDerived.{z} X U).obj (DerivedCategory.Q.obj L) ⟶
          (localizedRestrictionDerived.{z} X U).obj (DerivedCategory.Q.obj I)) :=
  (degreeAddEquiv X U L I 0).trans
    (Iso.homCongrAddEquiv (Iso.refl _)
      ((shiftFunctorZero (ModuleDerived.{z} (X.localization U)) ℤ).app
        ((localizedRestrictionDerived.{z} X U).obj (DerivedCategory.Q.obj I))))

/-- Transport the localized degree-`n` comparison across chosen ambient derived-category
representations of the source and target. -/
@[stacks 0CS5 "localized Hom-complex equivalence for represented objects"]
noncomputable def degreeAddEquivOfIso
    (L I : CochainComplex (ModuleCat.{z} X) ℤ) [I.IsKInjective]
    {K M : ModuleDerived.{z} X}
    (eL : DerivedCategory.Q.obj L ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ M) (n : ℤ) :
    (CochainComplex.HomComplex
      ((localizedRestrictionComplex.{z} X U).obj L)
      ((localizedRestrictionComplex.{z} X U).obj I)).homology n ≃+
        ((localizedRestrictionDerived.{z} X U).obj K ⟶
          ((localizedRestrictionDerived.{z} X U).obj M)⟦n⟧) :=
  (degreeAddEquiv X U L I n).trans
    (Iso.homCongrAddEquiv
      ((localizedRestrictionDerived.{z} X U).mapIso eL)
      (asIso
        (((localizedRestrictionDerived.{z} X U).mapIso eI).hom⟦n⟧')))

/-- Transport the localized degree-zero comparison across chosen ambient derived-category
representations of the source and target. -/
@[stacks 0A94 "localized Hom-complex equivalence for represented objects"]
noncomputable def zeroAddEquivOfIso
    (L I : CochainComplex (ModuleCat.{z} X) ℤ) [I.IsKInjective]
    {K M : ModuleDerived.{z} X}
    (eL : DerivedCategory.Q.obj L ≅ K)
    (eI : DerivedCategory.Q.obj I ≅ M) :
    (CochainComplex.HomComplex
      ((localizedRestrictionComplex.{z} X U).obj L)
      ((localizedRestrictionComplex.{z} X U).obj I)).homology (0 : ℤ) ≃+
        ((localizedRestrictionDerived.{z} X U).obj K ⟶
          (localizedRestrictionDerived.{z} X U).obj M) :=
  (zeroAddEquiv X U L I).trans
    (Iso.homCongrAddEquiv
      ((localizedRestrictionDerived.{z} X U).mapIso eL)
      ((localizedRestrictionDerived.{z} X U).mapIso eI))

end RingedSite.Hom.LocalizedRestriction.Homology
