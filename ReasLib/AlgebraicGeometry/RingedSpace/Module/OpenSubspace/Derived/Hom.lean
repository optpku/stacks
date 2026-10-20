/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Resolution.Hom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- Local instance justification (proof-local temporary data): homologyAddEquivOfIso uses restrictedComplexOnOpen X U Ic as its injective representative; the named restriction theorem supplies exactly this K-injective proof.
attribute [local instance] AlgebraicGeometry.RingedSpace.moduleRestrictionToOpen_isKInjective


/-!
# Derived Hom on open subspaces

This leaf combines the category-independent K-injective Hom-complex comparison with derived
restriction to an open subspace.  The root API is stated for arbitrary derived objects together
with chosen complex representatives; the chosen-preimage presentation is only a companion view.
-/

open AlgebraicGeometry CategoryTheory ComplexShape TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.OpenSubspace.Restriction

/-- The localization of a restricted representative identifies with the canonical derived
restriction of the represented object. -/
@[stacks 08DP "localization commutes with restriction to an open"]
noncomputable def qObjRestrictionIsoOfIso
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (K : CochainComplex (RingedSpace.Modules X) ℤ)
    {E : DerivedCategory (RingedSpace.Modules X)}
    (e : DerivedCategory.Q.obj K ≅ E) :
    DerivedCategory.Q.obj (restrictedComplexOnOpen X U K) ≅
      (moduleRestrictionToOpenDerived X U).obj E :=
  (moduleRestrictionToOpenDerivedFactors X U K).symm ≪≫
    (moduleRestrictionToOpenDerived X U).mapIso e

/-- The representative-level specialization of `qObjRestrictionIsoOfIso` for `Q.obj K`. -/
@[stacks 08DP "restricted complex representative"]
noncomputable def qObjRestrictionIso
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    DerivedCategory.Q.obj (restrictedComplexOnOpen X U K) ≅
      (moduleRestrictionToOpenDerived X U).obj (DerivedCategory.Q.obj K) :=
  qObjRestrictionIsoOfIso U K (Iso.refl _)

/-- Degree-`n` cohomology of a restricted Hom complex computes morphisms between arbitrary
canonical derived restrictions, after choosing representatives for both arguments. -/
@[stacks 0A8R "restricted Hom-complex cohomology as local shifted derived Hom"]
noncomputable def homologyAddEquivOfIso
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (Lc Ic : CochainComplex (RingedSpace.Modules X) ℤ) [Ic.IsKInjective]
    {L M : DerivedCategory (RingedSpace.Modules X)}
    (eL : DerivedCategory.Q.obj Lc ≅ L)
    (eI : DerivedCategory.Q.obj Ic ≅ M) (n : ℤ) :
    (CochainComplex.HomComplex
        (restrictedComplexOnOpen X U Lc)
        (restrictedComplexOnOpen X U Ic)).homology n ≃+
      ShiftedHom ((moduleRestrictionToOpenDerived X U).obj L)
        ((moduleRestrictionToOpenDerived X U).obj M) n :=
  CochainComplex.Resolution.injectiveHomologyAddEquivOfIso
    (restrictedComplexOnOpen X U Lc)
    (restrictedComplexOnOpen X U Ic)
    (qObjRestrictionIsoOfIso U Lc eL)
    (qObjRestrictionIsoOfIso U Ic eI) n

/-- Degree-zero specialization of `homologyAddEquivOfIso`. -/
@[stacks 0A8R "restricted Hom-complex degree-zero derived Hom"]
noncomputable def homologyZeroAddEquivOfIso
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (Lc Ic : CochainComplex (RingedSpace.Modules X) ℤ) [Ic.IsKInjective]
    {L M : DerivedCategory (RingedSpace.Modules X)}
    (eL : DerivedCategory.Q.obj Lc ≅ L)
    (eI : DerivedCategory.Q.obj Ic ≅ M) :
    (CochainComplex.HomComplex
        (restrictedComplexOnOpen X U Lc)
        (restrictedComplexOnOpen X U Ic)).homology (0 : ℤ) ≃+
      ((moduleRestrictionToOpenDerived X U).obj L ⟶
        (moduleRestrictionToOpenDerived X U).obj M) :=
  CochainComplex.Resolution.injectiveHomologyZeroAddEquivOfIso
    (restrictedComplexOnOpen X U Lc)
    (restrictedComplexOnOpen X U Ic)
    (qObjRestrictionIsoOfIso U Lc eL)
    (qObjRestrictionIsoOfIso U Ic eI)

/-- The source-facing degree-zero comparison as an isomorphism in `AddCommGrpCat`. -/
@[stacks 0A8R "restricted Hom-complex degree-zero derived Hom group"]
noncomputable def homologyZeroIsoOfIso
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (Lc Ic : CochainComplex (RingedSpace.Modules X) ℤ) [Ic.IsKInjective]
    {L M : DerivedCategory (RingedSpace.Modules X)}
    (eL : DerivedCategory.Q.obj Lc ≅ L)
    (eI : DerivedCategory.Q.obj Ic ≅ M) :
    (AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (AddCommGrpCat.of
          ((CochainComplex.HomComplex
            (restrictedComplexOnOpen X U Lc)
            (restrictedComplexOnOpen X U Ic)).homology (0 : ℤ))) ≅
      AddCommGrpCat.of
        (((moduleRestrictionToOpenDerived X U).obj L ⟶
          (moduleRestrictionToOpenDerived X U).obj M)) :=
  (AddEquiv.ulift.trans (homologyZeroAddEquivOfIso U Lc Ic eL eI)).toAddCommGrpIso

/- The intrinsic `K↾[U]` view is the source-facing target used throughout the chapter.  Keep this
companion next to the functorial form so clients do not rebuild the two endpoint transports. -/
/-- Degree-zero restricted Hom-complex cohomology, with both endpoints expressed in the intrinsic
chosen-complex view of derived restriction. -/
@[stacks 0A8R "intrinsic restricted Hom-complex additive equivalence"]
noncomputable def homologyZeroAddEquivOfIso_restricted
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (Lc Ic : CochainComplex (RingedSpace.Modules X) ℤ) [Ic.IsKInjective]
    {L M : DerivedCategory (RingedSpace.Modules X)}
    (eL : DerivedCategory.Q.obj Lc ≅ L)
    (eI : DerivedCategory.Q.obj Ic ≅ M) :
    (AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (AddCommGrpCat.of
          ((CochainComplex.HomComplex
            (restrictedComplexOnOpen X U Lc)
            (restrictedComplexOnOpen X U Ic)).homology (0 : ℤ))) ≃+
      (restrictedModuleDerivedOnOpen X U L ⟶ restrictedModuleDerivedOnOpen X U M) :=
  (AddEquiv.ulift.trans (homologyZeroAddEquivOfIso U Lc Ic eL eI)).trans
    (Iso.homCongrAddEquiv
      (OpenSubspace.Restriction.derivedObjIsoRestricted X U L)
      (OpenSubspace.Restriction.derivedObjIsoRestricted X U M))

/-- Lemma 20.41.6 (0A8R): restricted Hom-complex degree-zero cohomology computes morphisms
between the intrinsic derived restrictions of represented objects. -/
@[stacks 0A8R "intrinsic restricted derived-Hom comparison"]
theorem homologyZeroIsoOfIso_restricted
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (Lc Ic : CochainComplex (RingedSpace.Modules X) ℤ) [Ic.IsKInjective]
    {L M : DerivedCategory (RingedSpace.Modules X)}
    (eL : DerivedCategory.Q.obj Lc ≅ L)
    (eI : DerivedCategory.Q.obj Ic ≅ M) :
    IsIsomorphic
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (AddCommGrpCat.of
          ((CochainComplex.HomComplex
            (restrictedComplexOnOpen X U Lc)
            (restrictedComplexOnOpen X U Ic)).homology (0 : ℤ))))
      (AddCommGrpCat.of
        (restrictedModuleDerivedOnOpen X U L ⟶ restrictedModuleDerivedOnOpen X U M)) := sorry

/-- The representative-level degree-`n` comparison, with both derived objects presented by `Q`. -/
@[stacks 0A8R "restricted representative Hom-complex comparison"]
noncomputable def homologyAddEquiv
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (Lc Ic : CochainComplex (RingedSpace.Modules X) ℤ) [Ic.IsKInjective] (n : ℤ) :
    (CochainComplex.HomComplex
        (restrictedComplexOnOpen X U Lc)
        (restrictedComplexOnOpen X U Ic)).homology n ≃+
      ShiftedHom ((moduleRestrictionToOpenDerived X U).obj (DerivedCategory.Q.obj Lc))
        ((moduleRestrictionToOpenDerived X U).obj (DerivedCategory.Q.obj Ic)) n :=
  homologyAddEquivOfIso U Lc Ic (Iso.refl _) (Iso.refl _) n

/-- Representative-level degree-zero specialization of `homologyAddEquiv`. -/
@[stacks 0A8R "restricted representative degree-zero comparison"]
noncomputable def homologyZeroAddEquiv
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (Lc Ic : CochainComplex (RingedSpace.Modules X) ℤ) [Ic.IsKInjective] :
    (CochainComplex.HomComplex
        (restrictedComplexOnOpen X U Lc)
        (restrictedComplexOnOpen X U Ic)).homology (0 : ℤ) ≃+
      ((moduleRestrictionToOpenDerived X U).obj (DerivedCategory.Q.obj Lc) ⟶
        (moduleRestrictionToOpenDerived X U).obj (DerivedCategory.Q.obj Ic)) :=
  homologyZeroAddEquivOfIso U Lc Ic (Iso.refl _) (Iso.refl _)

end AlgebraicGeometry.RingedSpace.OpenSubspace.Restriction

end
