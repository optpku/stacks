/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PrincipalInternalHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.RingedSiteDerived
open SheafOfModules.RingedSite.ExtendedCech

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived.LocalizationAway

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- Multiplication by a global section on one objectwise module of a module sheaf. -/
noncomputable def actionApp
    (f : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    M.val.obj U ⟶ M.val.obj U :=
  ModuleCat.ofHom
    (LinearMap.lsmul (O.obj.obj U) (M.val.obj U) (sectionValue f U))

set_option backward.isDefEq.respectTransparency false in
/-- Objectwise multiplication by a global section commutes with restriction maps. -/
theorem actionApp_naturality
    (f : (unitModule J O).sections) (M : ringedSiteModuleCategory J O)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    M.val.map i ≫ (ModuleCat.restrictScalars (O.obj.map i).hom).map
        (actionApp f M V) =
      actionApp f M U ≫ M.val.map i := by
  ext x
  change sectionValue f V • (M.val.map i x : M.val.obj V) =
    M.val.map i (sectionValue f U • x)
  rw [M.val.map_smul]
  have hf : (O.obj.map i) (sectionValue f U) = sectionValue f V := f.property i
  exact congrArg (fun r ↦ r • (M.val.map i x : M.val.obj V)) hf.symm

/-- Multiplication by a global section as an endomorphism of a module sheaf. -/
noncomputable def actionHom
    (f : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) : M ⟶ M where
  val :=
    { app U := actionApp f M U
      naturality := actionApp_naturality f M }

/-- The component of the global-section action is objectwise scalar multiplication. -/
theorem actionHom_app
    (f : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    (actionHom f M).val.app U = actionApp f M U := rfl

/-- Module-sheaf morphisms commute with multiplication by a global section. -/
theorem actionHom_naturality
    (f : (unitModule J O).sections) {M N : ringedSiteModuleCategory J O} (g : M ⟶ N) :
    g ≫ actionHom f N = actionHom f M ≫ g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change sectionValue f U • g.val.app U x = g.val.app U (sectionValue f U • x)
  exact ((g.val.app U).hom.map_smul (sectionValue f U) x).symm

/-- Multiplication by a global section as a natural endomorphism of the identity functor. -/
noncomputable def actionNatTrans
    (f : (unitModule J O).sections) :
    𝟭 (ringedSiteModuleCategory J O) ⟶ 𝟭 (ringedSiteModuleCategory J O) where
  app M := actionHom f M
  naturality _ _ g := actionHom_naturality f g

/-- The component of the global-section natural endomorphism is `actionHom`. -/
theorem actionNatTrans_app
    (f : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) :
    (actionNatTrans f).app M = actionHom f M := rfl

/-- Multiplication by a global section as an endomorphism of the exact identity functor. -/
noncomputable def actionExact
    (f : (unitModule J O).sections) :
    ExactFunctor.id (ringedSiteModuleCategory J O) ⟶
      ExactFunctor.id (ringedSiteModuleCategory J O) :=
  ObjectProperty.homMk (P := exactFunctor _ _) (actionNatTrans f)

/-- The underlying natural transformation of the exact action is `actionNatTrans`. -/
theorem actionExact_hom
    (f : (unitModule J O).sections) :
    (actionExact f).hom = actionNatTrans f := rfl

/-- Multiplication by a global section on an object of `D(O)`. -/
noncomputable def action
    (f : (unitModule J O).sections) (K : max J O) : End K :=
  (ExactFunctor.MapDerivedCategory.idObjIso (ringedSiteModuleCategory J O) K).inv ≫
    (ExactFunctor.MapDerivedCategory.map (actionExact f)).app K ≫
      (ExactFunctor.MapDerivedCategory.idObjIso (ringedSiteModuleCategory J O) K).hom

/-- The derived global-section action is the conjugate of the exact-derived action by the
canonical identity comparison. -/
theorem action_eq
    (f : (unitModule J O).sections) (K : max J O) :
    action f K =
      (ExactFunctor.MapDerivedCategory.idObjIso (ringedSiteModuleCategory J O) K).inv ≫
        (ExactFunctor.MapDerivedCategory.map (actionExact f)).app K ≫
          (ExactFunctor.MapDerivedCategory.idObjIso
            (ringedSiteModuleCategory J O) K).hom := rfl

/-- The inverse system on `K` whose every transition is multiplication by `f`. -/
abbrev tower (f : (unitModule J O).sections) (K : max J O) :
    SequentialInverseSystem (max J O) :=
  Functor.ofOpSequence (X := fun _ ↦ K) (fun _ ↦ action f K)

/-- Every object of the localization-away tower is `K`. -/
theorem tower_obj
    (f : (unitModule J O).sections) (K : max J O) (n : ℕᵒᵖ) :
    (tower f K).obj n = K := rfl

/-- Every successor transition in the localization-away tower is multiplication by `f`. -/
theorem tower_map_succ
    (f : (unitModule J O).sections) (K : max J O) (n : ℕ) :
    (tower f K).map (homOfLE (Nat.le_add_right n 1)).op = action f K :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- Every derived internal Hom from a restricted `O_f`-complex to `K` vanishes. -/
def allInternalHomVanishing
    (f : (unitModule J O).sections)
    (K : max J O) : Prop :=
  ∀ L : max J (principalLocalization f),
    IsZero (RingedSite.Hom.ModuleDerived.InternalHom.obj
      ((principalRestrictionDerived f).obj L) K)

/-- Expansion of `allInternalHomVanishing` into its defining universal quantifier. -/
theorem allInternalHomVanishing_iff
    (f : (unitModule J O).sections)
    (K : max J O) :
    allInternalHomVanishing f K ↔
      ∀ L : max J (principalLocalization f),
        IsZero (RingedSite.Hom.ModuleDerived.InternalHom.obj
          ((principalRestrictionDerived f).obj L) K) := Iff.rfl

/-- The internal Hom from `O_f` is a homotopy limit of the multiplication-by-`f` tower. -/
theorem internalHom_isHomotopyLimit
    (f : (unitModule J O).sections)
    (K : max J O) :
    HomotopyLimit.IsOf (tower f K)
      (RingedSite.Hom.ModuleDerived.InternalHom.obj (principalDerivedModule f) K) := sorry

/-- Vanishing of `RHom_O(O_f, K)` is equivalent to vanishing of every
`RHom_O(L, K)` for `L ∈ D(O_f)`. -/
theorem internalHom_isZero_iff_all
    (f : (unitModule J O).sections)
    (K : max J O) :
    IsZero (RingedSite.Hom.ModuleDerived.InternalHom.obj (principalDerivedModule f) K) ↔
      allInternalHomVanishing f K := by
  constructor
  · intro h
    sorry
  · intro h
    exact h
      ((DerivedCategory.singleFunctor (ringedSiteModuleCategory J (principalLocalization f)) 0).obj
        (unitModule J (principalLocalization f)))

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of `RHom_O(O_f, K)` is equivalent to vanishing of any homotopy-limit
representative of the multiplication-by-`f` tower. -/
theorem internalHom_isZero_iff_limit
    (f : (unitModule J O).sections)
    (K T : max J O) (hT : HomotopyLimit.IsOf (tower f K) T) :
    IsZero (RingedSite.Hom.ModuleDerived.InternalHom.obj (principalDerivedModule f) K) ↔
      IsZero T := by
  obtain ⟨P, inclusionP, connectingP, distinguishedP⟩ := internalHom_isHomotopyLimit f K
  obtain ⟨Q, inclusionQ, connectingQ, distinguishedQ⟩ := hT
  let e := P.isLimit.conePointUniqueUpToIso Q.isLimit
  have he (n : ℕ) : e.hom ≫ SequentialInverseSystem.Milnor.ProductCone.projection Q (n) = SequentialInverseSystem.Milnor.ProductCone.projection P (n) :=
    P.isLimit.conePointUniqueUpToIso_hom_comp Q.isLimit ⟨n⟩
  have difference_fac (R : LimitCone (Discrete.functor (tower f K).family)) (n : ℕ) :
      SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) R ≫
          SequentialInverseSystem.Milnor.ProductCone.projection R (n) =
        SequentialInverseSystem.Milnor.ProductCone.projection R (n) - SequentialInverseSystem.Milnor.ProductCone.projection R (n + 1) ≫
          (tower f K).transitionMap (Nat.le_succ n) :=
    R.isLimit.fac _ ⟨n⟩
  have hd : SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) P ≫
        e.hom =
      e.hom ≫ SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) Q := by
    apply Q.isLimit.hom_ext
    rintro ⟨n⟩
    calc
      (SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) P ≫ e.hom) ≫
          SequentialInverseSystem.Milnor.ProductCone.projection Q (n) =
        SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) P ≫
          SequentialInverseSystem.Milnor.ProductCone.projection P (n) := by rw [Category.assoc, he]
      _ = SequentialInverseSystem.Milnor.ProductCone.projection P (n) - SequentialInverseSystem.Milnor.ProductCone.projection P (n + 1) ≫
          (tower f K).transitionMap (Nat.le_succ n) := difference_fac P n
      _ = e.hom ≫ (SequentialInverseSystem.Milnor.ProductCone.projection Q (n) - SequentialInverseSystem.Milnor.ProductCone.projection Q (n + 1) ≫
          (tower f K).transitionMap (Nat.le_succ n)) := by
        rw [Preadditive.comp_sub, ← Category.assoc, he, he]
      _ = (e.hom ≫ SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) Q) ≫
          SequentialInverseSystem.Milnor.ProductCone.projection Q (n) := by rw [Category.assoc, difference_fac]
  have hd_iso :
      IsIso (SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) P) ↔
        IsIso (SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) Q) := by
    simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using
      (show IsIso (SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) P ≫
          e.hom) ↔
        IsIso (e.hom ≫ SequentialInverseSystem.Milnor.ProductCone.difference (tower f K) Q)
        by rw [hd])
  exact (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ distinguishedP).trans
    (hd_iso.trans (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ distinguishedQ).symm)

/-- For a global section `f` and `K ∈ D(O)`, vanishing of `RHom_O(O_f, K)`,
vanishing of `RHom_O(L, K)` for every `L ∈ D(O_f)`, and vanishing of any homotopy-limit
representative of the multiplication-by-`f` tower are equivalent. -/
theorem vanishing_tfae
    (f : (unitModule J O).sections)
    (K T : max J O) (hT : HomotopyLimit.IsOf (tower f K) T) :
    List.TFAE
      [ IsZero (RingedSite.Hom.ModuleDerived.InternalHom.obj (principalDerivedModule f) K),
        allInternalHomVanishing f K,
        IsZero T ] := by
  rw [List.tfae_cons_cons, List.tfae_cons_cons]
  exact ⟨internalHom_isZero_iff_all f K,
    (internalHom_isZero_iff_all f K).symm.trans (internalHom_isZero_iff_limit f K T hT),
    List.tfae_singleton _⟩

end RingedSite.Hom.ModuleDerived.LocalizationAway
