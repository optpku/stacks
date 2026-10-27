/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Compactification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Forget
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [Ring Λ]
variable [IsSeparated X.hom] [Scheme.Hom.QuasiFinite X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Compactification.Of.ι P)).op]
-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The abelian compactification identification `f_! ≅ π_* ∘ j_!` after
transporting along `X.hom = ι P ≫ P.obj.right.hom`. -/
private def etaleAbelianLowerShriekCompactifyPushforwardIso :
    etaleLowerShriek X.hom ≅
      abelianExtensionByZero (Compactification.Of.ι P) ⋙
        etaleAbelianPushforward P.obj.right.hom :=
  etaleLowerShriekCompactifyIso_eq (Compactification.Of.ι P) P.obj.right.hom
      X.hom (Over.w P.obj.hom) ≪≫
    isoWhiskerLeft (abelianExtensionByZero (Compactification.Of.ι P))
      (etaleLowerShriekIso P.obj.right.hom)

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- Forgetting coefficients identifies `π_* (j_! F)` with
`π_*^{ab} (j_!^{ab} (forget F))`. -/
private def etaleModuleCompactifyPushforward_forgetLeft
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology).obj
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ)).obj F)) ≅
      (etaleAbelianPushforward P.obj.right.hom).obj
        ((abelianExtensionByZero (Compactification.Of.ι P)).obj
          ((sheafCompose X.left.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :=
  (eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose
      (smallEtalePullback P.obj.right.hom) (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
      Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology)).app
      ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)).obj F) ≪≫
    (etaleAbelianPushforward P.obj.right.hom).mapIso
      ((Functor.sheafPullback.compSheafComposeIso
          (etaleRestriction (Compactification.Of.ι P)) (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
          X.left.smallEtaleTopology P.obj.right.left.smallEtaleTopology).app F)

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- Forgetting coefficients identifies `f_! F` with `lowerShriek (forget F)`. -/
private def etaleModuleCompactifyPushforward_forgetRight
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule X.hom Λ).obj F) ≅
      (lowerShriek X.hom).obj
        ((sheafCompose X.left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) :=
  (lowerShriekModule_forgetFunctorIso X.hom Λ).app F

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The underlying additive hom map of the compactification comparison. -/
private def etaleModuleCompactifyPushforward_hom
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((etaleModuleCompactifyPushforward_forgetLeft X Λ P F).hom ≫
          ((etaleAbelianLowerShriekCompactifyPushforwardIso X P).symm.app
              ((sheafCompose X.left.smallEtaleTopology
                  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
          ((lowerShriekIso_separated X.hom).symm.app
              ((sheafCompose X.left.smallEtaleTopology
                  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
          (etaleModuleCompactifyPushforward_forgetRight X Λ F).inv)

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The underlying additive inv map of the compactification comparison. -/
private def etaleModuleCompactifyPushforward_inv
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((etaleModuleCompactifyPushforward_forgetRight X Λ F).hom ≫
          ((lowerShriekIso_separated X.hom).app
              ((sheafCompose X.left.smallEtaleTopology
                  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
          ((etaleAbelianLowerShriekCompactifyPushforwardIso X P).app
              ((sheafCompose X.left.smallEtaleTopology
                  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
          (etaleModuleCompactifyPushforward_forgetLeft X Λ P F).inv)

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The additive hom map of the compactification comparison respects scalar multiplication. -/
private theorem etaleModuleCompactifyPushforward_hom_smul
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : Y.Etaleᵒᵖ) (r : Λ) (x : (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology).obj
    ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)).obj F)).obj.obj U) :
    ((etaleModuleCompactifyPushforward_hom X Λ P F).hom.app U).hom (r • x) =
      HSMul.hSMul (α := Λ) (β := ((lowerShriekModule X.hom Λ).obj F).obj.obj U) (γ := ((lowerShriekModule X.hom Λ).obj F).obj.obj U)
        r (((etaleModuleCompactifyPushforward_hom X Λ P F).hom.app U).hom x) := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The scalar-compatible additive hom map as a morphism of module sheaves. -/
private def etaleModuleCompactifyPushforward_homModule
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology).obj
    ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)).obj F) ⟶ (lowerShriekModule X.hom Λ).obj F :=
  liftModuleSheafHom (etaleModuleCompactifyPushforward_hom X Λ P F)
    (etaleModuleCompactifyPushforward_hom_smul X Λ P F)

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The additive inv map of the compactification comparison respects scalar multiplication. -/
private theorem etaleModuleCompactifyPushforward_inv_smul
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : Y.Etaleᵒᵖ) (r : Λ) (x : ((lowerShriekModule X.hom Λ).obj F).obj.obj U) :
    ((etaleModuleCompactifyPushforward_inv X Λ P F).hom.app U).hom (r • x) =
      HSMul.hSMul (α := Λ) (β := (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology).obj
    ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)).obj F)).obj.obj U) (γ := (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology).obj
    ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)).obj F)).obj.obj U)
        r (((etaleModuleCompactifyPushforward_inv X Λ P F).hom.app U).hom x) := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The scalar-compatible additive inv map as a morphism of module sheaves. -/
private def etaleModuleCompactifyPushforward_invModule
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule X.hom Λ).obj F ⟶ ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology).obj
    ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)).obj F) :=
  liftModuleSheafHom (etaleModuleCompactifyPushforward_inv X Λ P F)
    (etaleModuleCompactifyPushforward_inv_smul X Λ P F)

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The two module comparison maps compose to the identity. -/
private theorem etaleModuleCompactifyPushforward_hom_inv_id
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleCompactifyPushforward_homModule X Λ P F ≫
      etaleModuleCompactifyPushforward_invModule X Λ P F = 𝟙 (((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology).obj
    ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ)).obj F)) := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The two module comparison maps compose to the identity. -/
private theorem etaleModuleCompactifyPushforward_inv_hom_id
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleCompactifyPushforward_invModule X Λ P F ≫
      etaleModuleCompactifyPushforward_homModule X Λ P F = 𝟙 ((lowerShriekModule X.hom Λ).obj F) := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The component identifying proper pushforward after extension by zero with compact-support direct image. -/
def etaleModuleLowerShriekCompactifyPushforwardIso_app
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology
        P.obj.right.left.smallEtaleTopology).obj
        ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} Λ)).obj F) ≅
      (lowerShriekModule X.hom Λ).obj F :=
  { hom := etaleModuleCompactifyPushforward_homModule X Λ P F
    inv := etaleModuleCompactifyPushforward_invModule X Λ P F
    hom_inv_id := etaleModuleCompactifyPushforward_hom_inv_id X Λ P F
    inv_hom_id := etaleModuleCompactifyPushforward_inv_hom_id X Λ P F }

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- The compactification comparison components are natural in module sheaves. -/
private theorem etaleModuleLowerShriekCompactifyPushforwardIso_naturality
    {F G : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)} (φ : F ⟶ G) :
    ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ) ⋙
        (smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology P.obj.right.left.smallEtaleTopology).map φ) ≫
        (etaleModuleLowerShriekCompactifyPushforwardIso_app X Λ P G).hom =
      (etaleModuleLowerShriekCompactifyPushforwardIso_app X Λ P F).hom ≫
        (lowerShriekModule X.hom Λ).map φ := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module elaborator
-- must retain these private comparison maps and laws in the public isomorphism implementation.
set_option backward.privateInPublic true in
/-- Sheaf-level compactification identification `π_* ∘ j_! ≅ f_!` on étale
sheaves of `Λ`-modules. -/
def etaleModuleLowerShriekCompactifyPushforwardIso :
    etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ) ⋙
        (smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          P.obj.right.left.smallEtaleTopology ≅
      lowerShriekModule X.hom Λ :=
  NatIso.ofComponents
    (etaleModuleLowerShriekCompactifyPushforwardIso_app X Λ P)
    (fun φ ↦ etaleModuleLowerShriekCompactifyPushforwardIso_naturality X Λ P φ)


end AlgebraicGeometry.Scheme.Etale

end
