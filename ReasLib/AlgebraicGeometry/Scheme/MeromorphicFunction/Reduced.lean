/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints.GenericPoints

/-!
# Meromorphic functions on reduced schemes

On a reduced scheme with finitely many irreducible components on quasi-compact opens, the
meromorphic-function sheaf is controlled by the residue fields at the generic points. Its stalks
and its sections on affine opens are total quotient rings.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The direct image on `X` of the structure sheaf of the spectrum of the residue field at a
generic point. -/
abbrev genericPointResidueFieldPushforwardSheaf
    (X : Scheme.{u}) (η : genericPoints X) : TopCat.Sheaf CommRingCat X.toTopCat :=
  (TopCat.Sheaf.pushforward CommRingCat (X.fromSpecResidueField η.1).base).obj
    (Spec (X.residueField η.1)).sheaf

/-- The product of the direct images of the residue-field structure sheaves at the generic
points of `X`. -/
abbrev genericPointResidueFieldPushforwardProductSheaf
    (X : Scheme.{u}) : TopCat.Sheaf CommRingCat X.toTopCat :=
  ∏ᶜ fun η : genericPoints X ↦ genericPointResidueFieldPushforwardSheaf X η

namespace Scheme.MeromorphicFunction.Reduced

/-- The canonical comparison between the meromorphic-function sheaf of a reduced scheme and
the product of the pushed-forward residue-field sheaves at its generic points. -/
noncomputable def sheafIsoGenericPointResidueFieldPushforwardProduct
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.toLocallyRingedSpace.meromorphicFunctionSheaf ≅
      genericPointResidueFieldPushforwardProductSheaf X := by
  refine Classical.choice
      (meromorphicFunctionSheaf_iso_genericPointStalkPushforwardProduct X
        (Scheme.weakAss_eq_genericPoints X).le) ≪≫ Limits.Pi.mapIso fun η ↦ ?_
  have hfield : IsField (X.presheaf.stalk η.1) :=
    isField_stalk_of_closure_mem_irreducibleComponents X η.1 η.2
  -- Local instance justification (proof-local temporary data): use the field structure at this generic point.
  letI : Field (X.presheaf.stalk η.1) := hfield.toField
  -- Local instance justification (proof-local temporary data): the residue map of a field is bijective.
  letI : IsIso (X.residue η.1) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨by
      rw [injective_iff_map_eq_zero]
      intro r hr
      change IsLocalRing.residue (X.presheaf.stalk η.1) r = 0 at hr
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.maximalIdeal_eq_bot,
        Ideal.mem_bot] at hr
      exact hr, X.residue_surjective η.1⟩
  let f := Spec.map (X.residue η.1)
  -- Local instance justification (proof-local temporary data): `Spec.map` preserves the residue isomorphism.
  letI : IsIso f := inferInstance
  let H : Spec (X.residueField η.1) ≅
      Spec (CommRingCat.of (X.presheaf.stalk η.1)) := asIso f
  let P := Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace ⋙
      SheafedSpace.forgetToPresheafedSpace
  let e := PresheafedSpace.sheafIsoOfIso (P.mapIso H)
  let e' : (Spec (CommRingCat.of (X.presheaf.stalk η.1))).sheaf ≅
      (TopCat.Sheaf.pushforward CommRingCat H.hom.base).obj
        (Spec (X.residueField η.1)).sheaf :=
    (TopCat.Sheaf.forget CommRingCat
      (Spec (CommRingCat.of (X.presheaf.stalk η.1))).toTopCat).preimageIso e
  let ecompPresheaf := TopCat.Presheaf.Pushforward.comp f.base
    (X.fromSpecStalk η.1).base (Spec (X.residueField η.1)).presheaf
  let ecomp :
      (TopCat.Sheaf.pushforward CommRingCat (f.base ≫ (X.fromSpecStalk η.1).base)).obj
          (Spec (X.residueField η.1)).sheaf ≅
        (TopCat.Sheaf.pushforward CommRingCat (X.fromSpecStalk η.1).base).obj
          ((TopCat.Sheaf.pushforward CommRingCat f.base).obj
            (Spec (X.residueField η.1)).sheaf) :=
    (TopCat.Sheaf.forget CommRingCat X.toTopCat).preimageIso ecompPresheaf
  change
    (TopCat.Sheaf.pushforward CommRingCat (X.fromSpecStalk η.1).base).obj
        (Spec (CommRingCat.of (X.presheaf.stalk η.1))).sheaf ≅
      (TopCat.Sheaf.pushforward CommRingCat
        ((Spec.map (X.residue η.1)).base ≫ (X.fromSpecStalk η.1).base)).obj
          (Spec (X.residueField η.1)).sheaf
  exact (TopCat.Sheaf.pushforward CommRingCat
      (X.fromSpecStalk η.1).base).mapIso e' ≪≫ ecomp.symm

/-- On a reduced scheme with locally finite irreducible components, the meromorphic-function
sheaf is isomorphic to the product of the pushed-forward residue-field sheaves at its generic
points. -/
theorem sheaf_iso_genericPointResidueFieldPushforwardProduct
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    IsIsomorphic X.toLocallyRingedSpace.meromorphicFunctionSheaf
      (genericPointResidueFieldPushforwardProductSheaf X) :=
  ⟨sheafIsoGenericPointResidueFieldPushforwardProduct X⟩

/-- On a reduced scheme with locally finite irreducible components, the meromorphic-function
algebra is quasicoherent as a module over the structure sheaf. -/
theorem sheaf_isQuasicoherent
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
      (SheafOfModules.unit
        (ringSheaf (Opens.grothendieckTopology X.toTopCat)
          X.toLocallyRingedSpace.meromorphicFunctionSheaf) :
        ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat)
          X.toLocallyRingedSpace.meromorphicFunctionSheaf)).IsQuasicoherent := sorry

/-- The meromorphic-function sheaf of a reduced scheme with locally finite irreducible
components, bundled as a quasicoherent algebra over its structure sheaf. -/
noncomputable def qcAlgebra
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] : X.QcAlgebraUnder :=
  ⟨Under.mk X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom,
    sheaf_isQuasicoherent X⟩

/-- At every point of a reduced scheme with locally finite irreducible components, the local
meromorphic denominators are exactly the non-zero-divisors. -/
theorem denominatorStalk_eq_nonZeroDivisors
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] (x : X) :
    meromorphicDenominatorStalk X x = nonZeroDivisors (X.presheaf.stalk x) := by
  exact meromorphicDenominatorStalk_eq_nonZeroDivisors X
    (Scheme.weakAss_eq_genericPoints X).le x

/-- At every point of a reduced scheme with locally finite irreducible components, the
meromorphic-function stalk is the localization of the local ring at its non-zero-divisors. -/
theorem stalk_isLocalization
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] (x : X) :
    IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk x) := by
  exact meromorphicStalk_isLocalization X (Scheme.weakAss_eq_genericPoints X).le x

/-- On every affine open of a reduced scheme with locally finite irreducible components,
meromorphic functions form the localization of regular functions at the non-zero-divisors. -/
theorem sections_isLocalization_of_isAffineOpen
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsLocalization (nonZeroDivisors Γ(X, U))
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.obj (op U)) := sorry

/-- On a reduced scheme with locally finite irreducible components, the rational-function ring
is isomorphic to the ring of global meromorphic functions. -/
theorem rationalFunctionRing_iso_meromorphicFunctions
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    IsIsomorphic X.rationalFunctionRing X.toLocallyRingedSpace.meromorphicFunctions := sorry

end Scheme.MeromorphicFunction.Reduced

end AlgebraicGeometry
