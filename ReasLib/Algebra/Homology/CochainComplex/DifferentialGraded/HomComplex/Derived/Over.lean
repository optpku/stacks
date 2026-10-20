/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.Derived
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.FunctorialResolution
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total

/-!
# Derived enriched Hom over an explicit base ring

This leaf is the reusable cochain-complex facade for an arbitrary commutative base ring `R`.
The cochain complexes still have integer cohomological grading, while their enriched Hom
objects live in `D(R)`.  Every call to the generic DG construction pins the canonical
`CochainComplex.differentialGradedCategory C R` owner explicitly; this keeps the `R`-linear
enrichment visible without installing a competing global instance.
-/

@[expose] public section

noncomputable section

universe r u v w x

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched.Over.RHom

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- The homotopy-level enriched Hom bifunctor for `R`-linear cochain complexes. -/
@[stacks 0CS6 "derived enriched Hom source over a base ring"]
noncomputable abbrev source :
    (DifferentialGradedCategory.K R (CochainComplex C ℤ))ᵒᵖ ×
        DifferentialGradedCategory.K R (CochainComplex C ℤ) ⥤
      DerivedCategory.{max r (v + 1)} (ModuleCat.{v} R) :=
  DifferentialGradedCategory.HomComplex.Derived.functor
    (R := R) (A := CochainComplex C ℤ)
    (DA := CochainComplex.differentialGradedCategory C R)

/-- The product quasi-isomorphism property used to derive both variables of `source`. -/
@[stacks 0CS6 "product quasi-isomorphisms for derived enriched Hom"]
abbrev qis :
    MorphismProperty
      ((DifferentialGradedCategory.K R (CochainComplex C ℤ))ᵒᵖ ×
        DifferentialGradedCategory.K R (CochainComplex C ℤ)) :=
  DifferentialGradedCategory.HomComplex.Derived.qis
    (DA := CochainComplex.differentialGradedCategory C R)
    (Over.quasiIso (R := R) (A := C))

/-- The localization of the two homotopy variables into an arbitrary derived category of `C`. -/
@[stacks 0CS6 "derived localization pair for enriched Hom"]
noncomputable abbrev localization [HasDerivedCategory.{w} C] :
    (DifferentialGradedCategory.K R (CochainComplex C ℤ))ᵒᵖ ×
        DifferentialGradedCategory.K R (CochainComplex C ℤ) ⥤
      (DerivedCategory.{w} C)ᵒᵖ × DerivedCategory.{w} C :=
  DifferentialGradedCategory.HomComplex.Derived.localization
    (DA := CochainComplex.differentialGradedCategory C R)
    (Over.derivedQ (R := R) (A := C))

/-- The existence condition for the total right-derived enriched Hom bifunctor. -/
@[stacks 0CS6 "existence of total derived enriched Hom"]
abbrev Has : Prop :=
  (source (R := R) (C := C)).HasPointwiseRightDerivedFunctor (qis (R := R) (C := C))

/-- A K-injective covariant entry computes simultaneous `R`-linear derived Hom independently of
the contravariant entry. -/
@[stacks 070Y "K-injective computation of explicit-base-ring derived Hom"]
theorem computesAt_of_kInjective (M I : CochainComplex C ℤ) [I.IsKInjective] :
    Functor.RightDerived.ComputesAt (source (R := R) (C := C)) (qis (R := R) (C := C))
      (Opposite.op
          (⟨M⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ)),
        (⟨I⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ))) := sorry

/-- Objectwise K-injective resolutions suffice for explicit-base-ring enriched derived Hom to
exist. -/
@[stacks 0CS6 "explicit-base-ring derived Hom from K-injective resolutions"]
theorem ofResolutions
    (h : ∀ K : CochainComplex C ℤ,
      Nonempty (_root_.CochainComplex.KInjectiveResolution K)) :
    Has (R := R) (C := C) := sorry

/-- A functorial K-injective resolution makes explicit-base-ring enriched derived Hom exist. -/
@[stacks 0CS6 "explicit-base-ring derived Hom from functorial resolutions"]
theorem ofFunctorialResolution
    (J : _root_.CochainComplex.KInjectiveResolution.Functorial C) :
    Has (R := R) (C := C) := sorry

/-- A Grothendieck abelian `R`-linear category has simultaneous derived enriched Hom. -/
@[stacks 0CS6 "existence of generic derived enriched Hom in a Grothendieck category"]
theorem hasRightDerivedFunctor [IsGrothendieckAbelian.{x} C] :
    Has (R := R) (C := C) := sorry

/-- The total derived enriched Hom bifunctor on arbitrary objects of `D(C)`. -/
@[stacks 0CS6 "total derived enriched Hom bifunctor"]
noncomputable abbrev functor [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] :
    (DerivedCategory.{w} C)ᵒᵖ × DerivedCategory.{w} C ⥤
      DerivedCategory.{max r (v + 1)} (ModuleCat.{v} R) :=
  DifferentialGradedCategory.HomComplex.Derived.RHom.functor
    (Over.derivedQ (R := R) (A := C))
    (Over.quasiIso (R := R) (A := C))
    (DA := CochainComplex.differentialGradedCategory C R)

/-- The curried total derived enriched Hom functor, with source variable first. -/
@[stacks 0CS6 "curried total derived enriched Hom"]
noncomputable abbrev curried [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] :
    (DerivedCategory.{w} C)ᵒᵖ ⥤ DerivedCategory.{w} C ⥤
      DerivedCategory.{max r (v + 1)} (ModuleCat.{v} R) :=
  DifferentialGradedCategory.HomComplex.Derived.RHom.curried
    (Over.derivedQ (R := R) (A := C))
    (Over.quasiIso (R := R) (A := C))
    (DA := CochainComplex.differentialGradedCategory C R)

/-- The total derived enriched Hom functor with a fixed target and varying source. -/
@[stacks 0CS6 "source-variable total derived enriched Hom"]
noncomputable abbrev sourceFunctor [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] (N : DerivedCategory.{w} C) :
    (DerivedCategory.{w} C)ᵒᵖ ⥤
      DerivedCategory.{max r (v + 1)} (ModuleCat.{v} R) :=
  DifferentialGradedCategory.HomComplex.Derived.RHom.sourceFunctor
    (Over.derivedQ (R := R) (A := C))
    (Over.quasiIso (R := R) (A := C)) N
    (DA := CochainComplex.differentialGradedCategory C R)

/-- The total derived enriched Hom functor with a fixed source and varying target. -/
@[stacks 0CS6 "target-variable total derived enriched Hom"]
noncomputable abbrev targetFunctor [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] (M : (DerivedCategory.{w} C)ᵒᵖ) :
    DerivedCategory.{w} C ⥤
      DerivedCategory.{max r (v + 1)} (ModuleCat.{v} R) :=
  DifferentialGradedCategory.HomComplex.Derived.RHom.targetFunctor
    (Over.derivedQ (R := R) (A := C))
    (Over.quasiIso (R := R) (A := C)) M
    (DA := CochainComplex.differentialGradedCategory C R)

/-- The universal map from homotopy-level enriched Hom to total derived enriched Hom. -/
@[stacks 0CS6 "unit for total derived enriched Hom"]
noncomputable abbrev unit [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] :
    source (R := R) (C := C) ⟶
      localization (R := R) (C := C) ⋙ functor (R := R) (C := C) :=
  DifferentialGradedCategory.HomComplex.Derived.RHom.unit
    (Over.derivedQ (R := R) (A := C))
    (Over.quasiIso (R := R) (A := C))
    (DA := CochainComplex.differentialGradedCategory C R)

/-- The explicit-base-ring derived-Hom unit evaluated on strict cochain complexes. -/
@[stacks 0CS6 "strict-complex component of explicit-base-ring derived Hom"]
noncomputable abbrev unitApp [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] (M N : CochainComplex C ℤ) :=
  (unit (R := R) (C := C)).app
    (Opposite.op
        (⟨M⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ)),
      (⟨N⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ)))

/-- A K-injective covariant entry makes the explicit-base-ring derived-Hom unit invertible. -/
@[stacks 070Y "K-injective explicit-base-ring derived-Hom unit isomorphism"]
theorem unitApp_isIso_of_kInjective [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] (M I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso (unitApp (R := R) (C := C) M I) := sorry

/-- The canonical isomorphism from strict `R`-linear Hom into a K-injective target to derived
enriched Hom. -/
@[stacks 070Y "K-injective strict model of explicit-base-ring derived Hom"]
noncomputable def unitAppIsoOfKInjective [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] (M I : CochainComplex C ℤ) [I.IsKInjective] :=
  @asIso _ _ _ _ (unitApp (R := R) (C := C) M I)
    (unitApp_isIso_of_kInjective (R := R) (C := C) M I)

/-- Replace the covariant member of a pair by a chosen K-injective resolution. -/
@[stacks 090Y "K-injective replacement for explicit-base-ring derived Hom"]
def replacement (M : CochainComplex C ℤ) {N : CochainComplex C ℤ}
    (I : _root_.CochainComplex.KInjectiveResolution N) :
    (Opposite.op
          (⟨M⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ)),
        (⟨N⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ))) ⟶
      (Opposite.op
          (⟨M⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ)),
        (⟨I.complex⟩ : DifferentialGradedCategory.K R (CochainComplex C ℤ))) :=
  (𝟙 _,
    @DifferentialGradedCategory.CompHom.toHomotopyClass R _ _
      (CochainComplex.differentialGradedCategory C R) _ _ (Over.ofHom (R := R) I.ι))

/-- K-injective replacement belongs to the product quasi-isomorphism system. -/
@[stacks 090Y "K-injective replacement is an explicit-base-ring RHom denominator"]
theorem replacement_mem (M : CochainComplex C ℤ) {N : CochainComplex C ℤ}
    (I : _root_.CochainComplex.KInjectiveResolution N) :
    qis (R := R) (C := C) (replacement (R := R) M I) := sorry

/-- A K-injective resolution gives the strict Hom-complex model of explicit-base-ring derived
Hom. -/
@[stacks 0CS6 "K-injective resolution model of explicit-base-ring derived Hom"]
noncomputable def resolutionModelIso [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] (M : CochainComplex C ℤ) {N : CochainComplex C ℤ}
    (I : _root_.CochainComplex.KInjectiveResolution N) :
    DerivedCategory.Q.obj (Over.homComplex (R := R) M I.complex) ≅
      (functor (R := R) (C := C)).obj
        (Opposite.op (DerivedCategory.Q.obj M), DerivedCategory.Q.obj N) :=
  Functor.RightDerived.ComputesAt.replacementIso
      (source (R := R) (C := C)) (qis (R := R) (C := C))
      (localization (R := R) (C := C))
      (replacement (R := R) M I) (replacement_mem (R := R) M I)
      (computesAt_of_kInjective (R := R) (C := C) M I.complex) ≪≫
    (functor (R := R) (C := C)).mapIso
      (Iso.prod
        (Over.derivedQObjIso (R := R) (A := C) M).symm.op
        (Over.derivedQObjIso (R := R) (A := C) N))

/-- The forward resolution-model comparison is the derived-Hom unit followed by transport to
the standard derived-category presentation. -/
@[simp, stacks 0CS6 "forward explicit-base-ring RHom resolution comparison"]
theorem resolutionModelIso_hom [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] (M : CochainComplex C ℤ) {N : CochainComplex C ℤ}
    (I : _root_.CochainComplex.KInjectiveResolution N) :
    (resolutionModelIso (R := R) (C := C) M I).hom =
      unitApp (R := R) (C := C) M I.complex ≫
        (functor (R := R) (C := C)).map
          (Localization.isoOfHom (localization (R := R) (C := C))
            (qis (R := R) (C := C)) (replacement (R := R) M I)
            (replacement_mem (R := R) M I)).inv ≫
        (functor (R := R) (C := C)).map
          (Iso.prod
            (Over.derivedQObjIso (R := R) (A := C) M).symm.op
            (Over.derivedQObjIso (R := R) (A := C) N)).hom := sorry

/-- The inverse resolution-model comparison first returns to the enriched localization
presentation and then uses the inverse K-injective unit. -/
@[simp, stacks 0CS6 "inverse explicit-base-ring RHom resolution comparison"]
theorem resolutionModelIso_inv [HasDerivedCategory.{w} C]
    [Has (R := R) (C := C)] (M : CochainComplex C ℤ) {N : CochainComplex C ℤ}
    (I : _root_.CochainComplex.KInjectiveResolution N) :
    (resolutionModelIso (R := R) (C := C) M I).inv =
      (functor (R := R) (C := C)).map
          (Iso.prod
            (Over.derivedQObjIso (R := R) (A := C) M).symm.op
            (Over.derivedQObjIso (R := R) (A := C) N)).inv ≫
        (functor (R := R) (C := C)).map
          (Localization.isoOfHom (localization (R := R) (C := C))
            (qis (R := R) (C := C)) (replacement (R := R) M I)
            (replacement_mem (R := R) M I)).hom ≫
        (unitAppIsoOfKInjective (R := R) (C := C) M I.complex).inv := sorry

end CategoryTheory.CochainComplex.Enriched.Over.RHom
