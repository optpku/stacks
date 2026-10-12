/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- Objectwise multiplication by a global section commutes with restriction maps. -/
theorem actionApp_naturality
    (f : (unitModule J O).sections) (M : ringedSiteModuleCategory J O)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    M.val.map i ≫ (ModuleCat.restrictScalars (O.obj.map i).hom).map
        (actionApp f M V) =
      actionApp f M U ≫ M.val.map i := sorry

/-- Multiplication by a global section as an endomorphism of a module sheaf. -/
noncomputable def actionHom
    (f : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) : M ⟶ M where
  val :=
    { app U := actionApp f M U
      naturality := actionApp_naturality f M }

/-- The component of the global-section action is objectwise scalar multiplication. -/
theorem actionHom_app
    (f : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    (actionHom f M).val.app U = actionApp f M U := sorry

/-- Module-sheaf morphisms commute with multiplication by a global section. -/
theorem actionHom_naturality
    (f : (unitModule J O).sections) {M N : ringedSiteModuleCategory J O} (g : M ⟶ N) :
    g ≫ actionHom f N = actionHom f M ≫ g := sorry

/-- Multiplication by a global section as a natural endomorphism of the identity functor. -/
noncomputable def actionNatTrans
    (f : (unitModule J O).sections) :
    𝟭 (ringedSiteModuleCategory J O) ⟶ 𝟭 (ringedSiteModuleCategory J O) where
  app M := actionHom f M
  naturality _ _ g := actionHom_naturality f g

/-- The component of the global-section natural endomorphism is `actionHom`. -/
theorem actionNatTrans_app
    (f : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) :
    (actionNatTrans f).app M = actionHom f M := sorry

/-- Multiplication by a global section as an endomorphism of the exact identity functor. -/
noncomputable def actionExact
    (f : (unitModule J O).sections) :
    ExactFunctor.id (ringedSiteModuleCategory J O) ⟶
      ExactFunctor.id (ringedSiteModuleCategory J O) :=
  ObjectProperty.homMk (P := exactFunctor _ _) (actionNatTrans f)

/-- The underlying natural transformation of the exact action is `actionNatTrans`. -/
theorem actionExact_hom
    (f : (unitModule J O).sections) :
    (actionExact f).hom = actionNatTrans f := sorry

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
            (ringedSiteModuleCategory J O) K).hom := sorry

/-- The inverse system on `K` whose every transition is multiplication by `f`. -/
abbrev tower (f : (unitModule J O).sections) (K : max J O) :
    SequentialInverseSystem (max J O) :=
  Functor.ofOpSequence (X := fun _ ↦ K) (fun _ ↦ action f K)

/-- Every object of the localization-away tower is `K`. -/
theorem tower_obj
    (f : (unitModule J O).sections) (K : max J O) (n : ℕᵒᵖ) :
    (tower f K).obj n = K := sorry

/-- Every successor transition in the localization-away tower is multiplication by `f`. -/
theorem tower_map_succ
    (f : (unitModule J O).sections) (K : max J O) (n : ℕ) :
    (tower f K).map (homOfLE (Nat.le_add_right n 1)).op = action f K := sorry

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
          ((principalRestrictionDerived f).obj L) K) := sorry

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
      allInternalHomVanishing f K := sorry

/-- Vanishing of `RHom_O(O_f, K)` is equivalent to vanishing of any homotopy-limit
representative of the multiplication-by-`f` tower. -/
theorem internalHom_isZero_iff_limit
    (f : (unitModule J O).sections)
    (K T : max J O) (hT : HomotopyLimit.IsOf (tower f K) T) :
    IsZero (RingedSite.Hom.ModuleDerived.InternalHom.obj (principalDerivedModule f) K) ↔
      IsZero T := sorry

/-- For a global section `f` and `K ∈ D(O)`, vanishing of `RHom_O(O_f, K)`,
vanishing of `RHom_O(L, K)` for every `L ∈ D(O_f)`, and vanishing of any homotopy-limit
representative of the multiplication-by-`f` tower are equivalent. -/
theorem vanishing_tfae
    (f : (unitModule J O).sections)
    (K T : max J O) (hT : HomotopyLimit.IsOf (tower f K) T) :
    List.TFAE
      [ IsZero (RingedSite.Hom.ModuleDerived.InternalHom.obj (principalDerivedModule f) K),
        allInternalHomVanishing f K,
        IsZero T ] := sorry

end RingedSite.Hom.ModuleDerived.LocalizationAway
