/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Spec.BasicOpen.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Spec.Stalk

/-!
# The tilde sheaf on principal opens and stalks

This file exposes concrete localization equivalences for an affine tilde
module and the compatibility of the principal-open equivalences with
restriction.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.tilde

variable {R : CommRingCat.{u}}

/-- The canonical localization comparison on `D(f)` is semilinear over the principal-open
sections isomorphism. -/
theorem basicOpenComparison_smul (M : ModuleCat R) (f : R)
    (r : Localization.Away f) (x : LocalizedModule.Away f M) :
    IsLocalizedModule.iso (.powers f) (toOpen M (PrimeSpectrum.basicOpen f)).hom (r • x) =
      ((tilde M).smul ((Spec.BasicOpen.sectionsIso f) r)).hom
        (IsLocalizedModule.iso (.powers f)
          (toOpen M (PrimeSpectrum.basicOpen f)).hom x) := sorry

/-- Lemma 26.5.4: sections of `M̃` on `D(f)` identify with `M_f`, as modules over the
canonical ring isomorphism `R_f ≃ Γ(D(f), 𝒪)`. -/
@[stacks 01HV]
noncomputable def basicOpenIso (M : ModuleCat R) (f : R) :
    LocalizedModule.Away f M ≃ₛₗ[
      (Spec.BasicOpen.sectionsIso f).toRingEquiv.toRingHom]
      Γ(tilde M, PrimeSpectrum.basicOpen f) :=
  { (IsLocalizedModule.iso (.powers f)
      (toOpen M (PrimeSpectrum.basicOpen f)).hom).toAddEquiv with
    map_smul' := basicOpenComparison_smul M f }

/-- The basic-open equivalence carries the canonical localized image of a module element to its
canonical tilde section. -/
@[simp, stacks 01HV "principal-open localization element"]
theorem basicOpenIso_mkLinearMap (M : ModuleCat R) (f : R) (m : M) :
    basicOpenIso M f (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      toOpen M (PrimeSpectrum.basicOpen f) m := sorry

/-- Under `basicOpenIso`, restriction of `M̃` is the canonical semilinear localization
comparison. This pointwise form avoids exposing scalar-transport casts. -/
@[stacks 01HV]
theorem basicOpenIso_restriction (M : ModuleCat R) {f g : R}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (x : LocalizedModule.Away f M) :
    (tilde M).val.restrictₛₗ (homOfLE h).op (basicOpenIso M f x) =
      basicOpenIso M g (PrimeSpectrum.awayToAwayModuleMap M f g h x) := sorry

/-- The principal-open localization equivalence is natural in the module. -/
@[simp, stacks 01HV "principal-open localization naturality"]
theorem basicOpenIso_naturality {M N : ModuleCat R} (phi : M ⟶ N) (f : R)
    (x : LocalizedModule.Away f M) :
    basicOpenIso N f (LocalizedModule.map (Submonoid.powers f) phi.hom x) =
      ((tilde.map phi).app (PrimeSpectrum.basicOpen f)).hom (basicOpenIso M f x) := sorry

/-- The canonical localization comparison at a prime is semilinear over the affine
structure-sheaf stalk isomorphism. -/
theorem stalkComparison_smul (M : ModuleCat R) (x : PrimeSpectrum R)
    (r : Localization.AtPrime x.asIdeal)
    (m : LocalizedModule x.asIdeal.primeCompl M) :
    IsLocalizedModule.iso x.asIdeal.primeCompl (toStalk M x).hom (r • m) =
      (((SheafOfModules.stalkFunctorOfCommRing
        (Spec.structureSheaf R) x).obj (tilde M)).smul
          ((StructureSheaf.stalkIso R x) r)).hom
        (IsLocalizedModule.iso x.asIdeal.primeCompl (toStalk M x).hom m) := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 26.5.4: the stalk of `M̃` at `x` identifies with localization at the corresponding
prime, as modules over the canonical ring isomorphism `R_p ≃ 𝒪_p`. -/
@[stacks 01HV]
noncomputable def stalkIso (M : ModuleCat R) (x : PrimeSpectrum R) :
    LocalizedModule x.asIdeal.primeCompl M ≃ₛₗ[
      (StructureSheaf.stalkIso R x).toRingEquiv.toRingHom]
      (SheafOfModules.stalkFunctorOfCommRing
        (Spec.structureSheaf R) x).obj (tilde M) :=
  { (IsLocalizedModule.iso x.asIdeal.primeCompl (toStalk M x).hom).toAddEquiv with
    map_smul' := stalkComparison_smul M x }

/-- The stalk equivalence carries the canonical localized image of a module element to its germ
in the tilde stalk. -/
@[simp, stacks 01HV "stalk localization element"]
theorem stalkIso_mkLinearMap (M : ModuleCat R) (x : PrimeSpectrum R) (m : M) :
    stalkIso M x (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M m) =
      toStalk M x m := sorry

/-- The stalk localization equivalence is natural in the module. -/
@[simp, stacks 01HV "stalk localization naturality"]
theorem stalkIso_naturality {M N : ModuleCat R} (phi : M ⟶ N)
    (x : PrimeSpectrum R) (m : LocalizedModule x.asIdeal.primeCompl M) :
    stalkIso N x (LocalizedModule.map x.asIdeal.primeCompl phi.hom m) =
      ((SheafOfModules.stalkFunctorOfCommRing
        (Spec.structureSheaf R) x).map (tilde.map phi)).hom (stalkIso M x m) := sorry

end AlgebraicGeometry.tilde
