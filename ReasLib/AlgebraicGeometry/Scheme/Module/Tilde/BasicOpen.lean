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
          (toOpen M (PrimeSpectrum.basicOpen f)).hom x) := by
  letI : Module (Localization.Away f) Γ(tilde M, PrimeSpectrum.basicOpen f) :=
    Module.compHom _ (Spec.BasicOpen.sectionsIso f).toRingHom
  haveI : IsScalarTower R (Localization.Away f)
      Γ(tilde M, PrimeSpectrum.basicOpen f) :=
    .of_algebraMap_smul fun a m ↦ by
      change Spec.BasicOpen.sectionsIso f (algebraMap R _ a) • m = a • m
      rw [AlgEquiv.commutes, IsScalarTower.algebraMap_smul]
  exact (IsLocalization.linearMap_compatibleSMul (.powers f) (Localization.Away f)
    (LocalizedModule.Away f M) Γ(tilde M, PrimeSpectrum.basicOpen f)).map_smul
      (IsLocalizedModule.iso (.powers f)
        (toOpen M (PrimeSpectrum.basicOpen f)).hom).toLinearMap r x

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
      toOpen M (PrimeSpectrum.basicOpen f) m := by
  exact IsLocalizedModule.iso_mk_one (.powers f)
    (toOpen M (PrimeSpectrum.basicOpen f)).hom m

set_option backward.isDefEq.respectTransparency false in
/-- Under `basicOpenIso`, restriction of `M̃` is the canonical semilinear localization
comparison. This pointwise form avoids exposing scalar-transport casts. -/
@[stacks 01HV]
theorem basicOpenIso_restriction (M : ModuleCat R) {f g : R}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (x : LocalizedModule.Away f M) :
    (tilde M).val.restrictₛₗ (homOfLE h).op (basicOpenIso M f x) =
      basicOpenIso M g (PrimeSpectrum.awayToAwayModuleMap M f g h x) := by
  let res := ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE h).op).hom
  let j := (IsLocalizedModule.iso (.powers f)
    (toOpen M (PrimeSpectrum.basicOpen f)).hom).toLinearMap
  let k := (IsLocalizedModule.iso (.powers g)
    (toOpen M (PrimeSpectrum.basicOpen g)).hom).toLinearMap
  have heq : res.comp j = k.comp (PrimeSpectrum.awayToAwayModuleLinearMap M f g h) := by
    apply IsLocalizedModule.ext (.powers f) (LocalizedModule.mkLinearMap (.powers f) M)
    · let L := (modulesSpecToSheaf.obj (tilde M)).presheaf.obj
        (.op (PrimeSpectrum.basicOpen g))
      letI : Module (Localization.Away g) L :=
        IsLocalizedModule.module (.powers g) (toOpen M (PrimeSpectrum.basicOpen g)).hom
      letI : IsScalarTower R (Localization.Away g) L :=
        IsLocalizedModule.isScalarTower_module (.powers g)
          (toOpen M (PrimeSpectrum.basicOpen g)).hom
      rintro ⟨_, ⟨n, rfl⟩⟩
      rw [← (Algebra.lsmul R (A := Localization.Away g) R L).commutes]
      simpa only [map_pow] using
        ((PrimeSpectrum.algebraMap_isUnit_of_basicOpen_le f g h).pow n).map
          (Algebra.lsmul R (A := Localization.Away g) R L)
    · ext m
      change res (j (LocalizedModule.mk m 1)) =
        k (PrimeSpectrum.awayToAwayModuleMap M f g h
          (LocalizedModule.mkLinearMap (.powers f) M m))
      rw [PrimeSpectrum.awayToAwayModuleMap_mkLinearMap]
      simp only [j, k, LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe,
        IsLocalizedModule.iso_mk_one]
      exact congr($(toOpen_res M _ _ (homOfLE h)) m)
  exact LinearMap.congr_fun heq x

set_option backward.isDefEq.respectTransparency false in
/-- The principal-open localization equivalence is natural in the module. -/
@[simp, stacks 01HV "principal-open localization naturality"]
theorem basicOpenIso_naturality {M N : ModuleCat R} (phi : M ⟶ N) (f : R)
    (x : LocalizedModule.Away f M) :
    basicOpenIso N f (LocalizedModule.map (Submonoid.powers f) phi.hom x) =
      ((tilde.map phi).app (PrimeSpectrum.basicOpen f)).hom (basicOpenIso M f x) := by
  let j := (IsLocalizedModule.iso (.powers f)
    (toOpen N (PrimeSpectrum.basicOpen f)).hom).toLinearMap
  let k := (IsLocalizedModule.iso (.powers f)
    (toOpen M (PrimeSpectrum.basicOpen f)).hom).toLinearMap
  let F := ((modulesSpecToSheaf.map (tilde.map phi)).1.app
    (.op (PrimeSpectrum.basicOpen f))).hom
  have heq : j.comp ((LocalizedModule.map (.powers f) phi.hom).restrictScalars R) =
      F.comp k := by
    apply IsLocalizedModule.linearMap_ext (.powers f)
      (LocalizedModule.mkLinearMap (.powers f) M)
      (toOpen N (PrimeSpectrum.basicOpen f)).hom
    ext m
    change j (IsLocalizedModule.map (.powers f)
      (LocalizedModule.mkLinearMap (.powers f) M)
      (LocalizedModule.mkLinearMap (.powers f) N) phi.hom (LocalizedModule.mk m 1)) =
        F (k (LocalizedModule.mk m 1))
    simp only [IsLocalizedModule.map_LocalizedModules, j, k, LinearEquiv.coe_coe,
      IsLocalizedModule.iso_mk_one]
    exact congr($(toOpen_map_app phi (PrimeSpectrum.basicOpen f)) m).symm
  exact LinearMap.congr_fun heq x

set_option backward.isDefEq.respectTransparency false in
/-- The canonical localization comparison at a prime is semilinear over the affine
structure-sheaf stalk isomorphism. -/
theorem stalkComparison_smul (M : ModuleCat R) (x : PrimeSpectrum R)
    (r : Localization.AtPrime x.asIdeal)
    (m : LocalizedModule x.asIdeal.primeCompl M) :
    IsLocalizedModule.iso x.asIdeal.primeCompl (toStalk M x).hom (r • m) =
      (((SheafOfModules.stalkFunctorOfCommRing
        (Spec.structureSheaf R) x).obj (tilde M)).smul
          ((StructureSheaf.stalkIso R x) r)).hom
        (IsLocalizedModule.iso x.asIdeal.primeCompl (toStalk M x).hom m) := by
  let N := PresheafOfModules.stalkModuleCatOfCommRing
    (𝒪c := (Spec.structureSheaf R).presheaf) (tilde M).val x
  letI : Module R N := inferInstanceAs (Module R ((tilde M).presheaf.stalk x))
  letI : Module (Localization.AtPrime x.asIdeal) N :=
    Module.compHom _ (StructureSheaf.stalkIso R x).toRingHom
  haveI : IsScalarTower R (Localization.AtPrime x.asIdeal) N :=
    .of_algebraMap_smul fun a n ↦ by
      change StructureSheaf.stalkIso R x (algebraMap R _ a) • n = a • n
      rw [AlgEquiv.commutes]
      rfl
  exact (IsLocalization.linearMap_compatibleSMul x.asIdeal.primeCompl
    (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl M) N).map_smul
      (IsLocalizedModule.iso x.asIdeal.primeCompl (toStalk M x).hom).toLinearMap r m

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
      toStalk M x m := by
  exact IsLocalizedModule.iso_mk_one x.asIdeal.primeCompl (toStalk M x).hom m

set_option backward.isDefEq.respectTransparency false in
/-- The stalk localization equivalence is natural in the module. -/
@[simp, stacks 01HV "stalk localization naturality"]
theorem stalkIso_naturality {M N : ModuleCat R} (phi : M ⟶ N)
    (x : PrimeSpectrum R) (m : LocalizedModule x.asIdeal.primeCompl M) :
    stalkIso N x (LocalizedModule.map x.asIdeal.primeCompl phi.hom m) =
      ((SheafOfModules.stalkFunctorOfCommRing
        (Spec.structureSheaf R) x).map (tilde.map phi)).hom (stalkIso M x m) := by
  have hgerm (P : ModuleCat R) (U : Opens (PrimeSpectrum R)) (hx : x ∈ U)
      (r : R) (s : Γ(tilde P, U)) :
      TopCat.Presheaf.germ (tilde P).presheaf U x hx (r • s) =
        r • TopCat.Presheaf.germ (tilde P).presheaf U x hx s := by
    letI : Module ((Spec.structureSheaf R).presheaf.stalk x) ((tilde P).presheaf.stalk x) :=
      inferInstanceAs (Module ((Spec.structureSheaf R).presheaf.stalk x)
        (PresheafOfModules.stalkModuleCatOfCommRing
          (𝒪c := (Spec.structureSheaf R).presheaf) (tilde P).val x))
    change TopCat.Presheaf.germ (tilde P).presheaf U x hx (r • s) =
      (algebraMap R ((Spec.structureSheaf R).presheaf.stalk x) r) •
        TopCat.Presheaf.germ (tilde P).presheaf U x hx s
    rw [StructureSheaf.stalkAlgebra_map, ← StructureSheaf.algebraMap_germ_apply U x hx]
    have hs := PresheafOfModules.germ_smul
      (R := (Spec.structureSheaf R).presheaf) (tilde P).val x U hx
      (algebraMap R ((structureSheafInType R R).obj.obj (.op U)) r) s
    exact hs
  let F₀ : (tilde M).presheaf.stalk x ⟶ (tilde N).presheaf.stalk x :=
    (TopCat.Presheaf.stalkFunctor (X := Spec R) AddCommGrpCat.{u} x).map (tilde.map phi).mapPresheaf
  have hF₀ (U : Opens (PrimeSpectrum R)) (hx : x ∈ U) (s : Γ(tilde M, U)) :
      F₀ (TopCat.Presheaf.germ (tilde M).presheaf U x hx s) =
        TopCat.Presheaf.germ (tilde N).presheaf U x hx ((tilde.map phi).app U s) := by
    exact congr($(TopCat.Presheaf.stalkFunctor_map_germ U x hx
      (tilde.map phi).mapPresheaf) s)
  let F : ((tilde M).presheaf.stalk x) →ₗ[R] ((tilde N).presheaf.stalk x) :=
    { toFun := F₀
      map_add' := F₀.hom.map_add
      map_smul' := fun r n ↦ by
        obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (tilde M).presheaf n
        rw [← hgerm M U hx r s]
        change F₀ (TopCat.Presheaf.germ (tilde M).presheaf U x hx (r • s)) =
          r • F₀ (TopCat.Presheaf.germ (tilde M).presheaf U x hx s)
        rw [hF₀ U hx, hF₀ U hx]
        let P := ((modulesSpecToSheaf.map (tilde.map phi)).1.app (.op U)).hom
        change TopCat.Presheaf.germ (tilde N).presheaf U x hx (P (r • s)) =
          r • TopCat.Presheaf.germ (tilde N).presheaf U x hx (P s)
        rw [P.map_smul r s, hgerm N U hx] }
  let j := (IsLocalizedModule.iso x.asIdeal.primeCompl (tilde.toStalk N x).hom).toLinearMap
  let k := (IsLocalizedModule.iso x.asIdeal.primeCompl (tilde.toStalk M x).hom).toLinearMap
  have heq : j.comp ((LocalizedModule.map x.asIdeal.primeCompl phi.hom).restrictScalars R) =
      F.comp k := by
    apply IsLocalizedModule.linearMap_ext x.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M) (tilde.toStalk N x).hom
    ext n
    change j (IsLocalizedModule.map x.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl N) phi.hom (LocalizedModule.mk n 1)) =
        F (k (LocalizedModule.mk n 1))
    simp only [IsLocalizedModule.map_LocalizedModules, j, k, LinearEquiv.coe_coe,
      IsLocalizedModule.iso_mk_one]
    change TopCat.Presheaf.germ (tilde N).presheaf ⊤ x trivial
        (tilde.toOpen N ⊤ (phi n)) =
      F₀ (TopCat.Presheaf.germ (tilde M).presheaf ⊤ x trivial (tilde.toOpen M ⊤ n))
    rw [hF₀ ⊤ trivial]
    exact congrArg (TopCat.Presheaf.germ (tilde N).presheaf ⊤ x trivial)
      congr($(tilde.toOpen_map_app phi ⊤) n).symm
  change j ((LocalizedModule.map x.asIdeal.primeCompl phi.hom) m) = F (k m)
  exact LinearMap.congr_fun heq m

end AlgebraicGeometry.tilde
