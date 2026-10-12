/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

/-!
# Finite-type modules on affine opens

This module relates finite type of a quasicoherent module sheaf to finite generation of its
sections on affine open subschemes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction of a finite-type module sheaf along an open immersion is of finite type. -/
instance restrict_obj_isFiniteType_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsFiniteType] :
    ((restrictFunctor f).obj M).IsFiniteType := by
  let g := RingedSpace.opensRingedSiteHom f.toLRSHom.toShHom
  -- Local instance justification (proof-local temporary data): finality supplies the finite-type pullback instance used only to compare restriction with pullback.
  letI : g.base.Final := CategoryTheory.final_of_representablyFlat g.base
  have h : ((pullback f).obj M).IsFiniteType := by
    change (g.modulePullback.obj M).IsFiniteType
    infer_instance
  -- Local instance justification (proof-local temporary data): transport the proved pullback property across the canonical restriction-pullback isomorphism.
  letI : ((pullback f).obj M).IsFiniteType := h
  exact SheafOfModules.isFiniteType_of_iso
    ((restrictFunctorIsoPullback f).app M).symm

/-- The affine chart map identifies its top-open global-functions isomorphism with the
canonical global-functions isomorphism of an affine scheme. -/
private lemma fromSpecGammaIsoTop {X : Scheme.{u}} (U : X.affineOpens) :
    let g := U.2.fromSpec
    let hImage : g ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U.1 :=
      g.image_top_eq_opensRange.trans U.2.opensRange_fromSpec
    (g.appIso ⊤).symm ≪≫ X.presheaf.mapIso (eqToIso hImage).symm.op =
      Scheme.ΓSpecIso Γ(X, U) := by
  dsimp only
  let g := U.2.fromSpec
  let hImage : g ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U.1 :=
    g.image_top_eq_opensRange.trans U.2.opensRange_fromSpec
  apply Iso.ext
  rw [← cancel_mono (Scheme.ΓSpecIso Γ(X, U)).inv]
  simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id]
  let q := (Spec Γ(X, U)).presheaf.map (eqToHom U.2.fromSpec_preimage_self).op
  rw [← cancel_mono q, Category.id_comp]
  simp only [Category.assoc]
  rw [← U.2.fromSpec_app_self]
  simp only [Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.inv]
  change (g.appIso ⊤).inv ≫ X.presheaf.map (eqToHom hImage.symm).op ≫
    g.app U.1 = q
  rw [g.naturality]
  rw [Scheme.Hom.appIso_inv_app_assoc]
  rw [← Functor.map_comp]
  rfl

/-- On an affine open, the global sections of a module sheaf agree with the global sections
of its restriction to the associated affine scheme. -/
noncomputable def affineOpenSectionsIso {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) :
    (moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((restrictFunctor U.2.fromSpec).obj M) ≅
      ModuleCat.of Γ(X, U) Γ(M, U.1) := by
  let g := U.2.fromSpec
  let hImage : g ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U.1 :=
    g.image_top_eq_opensRange.trans U.2.opensRange_fromSpec
  let eAdd :
      (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
          ((moduleSpecΓFunctor (R := Γ(X, U))).obj
            ((restrictFunctor g).obj M)) ≅
        (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
          (ModuleCat.of Γ(X, U) Γ(M, U.1)) :=
    M.restrictAppIso g ⊤ ≪≫
      M.presheaf.mapIso (eqToIso hImage).symm.op
  exact ModuleCat.isoMk eAdd (by
    intro r
    ext x
    let N := (restrictFunctor g).obj M
    let xN : Γ(N, (⊤ : (Spec Γ(X, U)).Opens)) := x
    change r • (M.presheaf.map (eqToHom hImage.symm).op
      ((M.restrictAppIso g ⊤).hom xN)) =
      M.presheaf.map (eqToHom hImage.symm).op
        ((M.restrictAppIso g ⊤).hom
          (((Scheme.ΓSpecIso Γ(X, U)).inv.hom r) • xN))
    rw [smul_restrictAppIso_hom_apply]
    rw [M.map_smul]
    have hRing := congrArg Iso.hom (fromSpecGammaIsoTop U)
    have hr := congrArg
      (fun f => f.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom r)) hRing
    simp only [Iso.trans_hom, CommRingCat.hom_comp, Iso.inv_hom_id_apply] at hr
    exact congrArg
      (fun s : Γ(X, U) => s •
        (M.presheaf.map (eqToHom hImage.symm).op
          ((M.restrictAppIso g ⊤).hom xN))) hr.symm)

/-- The sections of a finite-type quasicoherent module sheaf on an affine open form a finite
module over the ring of functions on that open. -/
instance affineOpen_sections_finite_of_isFiniteType {X : Scheme.{u}} (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] (U : X.affineOpens) :
    Module.Finite Γ(X, U) Γ(M, U.1) := by
  let N := (restrictFunctor U.2.fromSpec).obj M
  -- Local instance justification (proof-local temporary data): quasicoherence of the restricted module is needed only for the affine tilde comparison below.
  letI : N.IsQuasicoherent := inferInstance
  have hN : N.IsFiniteType := inferInstance
  -- Local instance justification (proof-local temporary data): install the restriction fact to invoke the affine tilde finite-type equivalence.
  letI : N.IsFiniteType := hN
  have hfinite :
      Module.Finite Γ(X, U) ((moduleSpecΓFunctor (R := Γ(X, U))).obj N) := by
    let hIso : IsIso (fromTildeΓ (R := Γ(X, U)) N) := inferInstance
    let e : tilde ((moduleSpecΓFunctor (R := Γ(X, U))).obj N) ≅ N :=
      @asIso _ _ _ _ (fromTildeΓ (R := Γ(X, U)) N) hIso
    have hTilde :
        (tilde ((moduleSpecΓFunctor (R := Γ(X, U))).obj N)).IsFiniteType :=
      SheafOfModules.isFiniteType_of_iso e.symm
    exact (tilde_isFiniteType_iff_module_finite _).mp hTilde
  exact (Module.Finite.equiv_iff (affineOpenSectionsIso M U).toLinearEquiv).mp hfinite

end AlgebraicGeometry.Scheme.Modules
