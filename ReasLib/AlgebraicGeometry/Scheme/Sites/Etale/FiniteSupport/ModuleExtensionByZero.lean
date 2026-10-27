/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Forget
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [LocallyQuasiFinite j]
variable (Λ : Type u) [Ring Λ]
variable [U.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- Forgetting coefficients identifies module extension by zero with the
underlying abelian sheaf of module-valued finite-support direct image. -/
private def moduleExtensionByZeroUnderlyingIso
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F) ≅
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule j Λ).obj F) :=
  (Functor.sheafPullback.compSheafComposeIso
    (etaleRestriction j) (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
    U.smallEtaleTopology X.smallEtaleTopology).app F ≪≫
  (extensionByZeroIsoLowerShriek j).app
    ((sheafCompose U.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) ≪≫
  ((lowerShriekModule_forgetFunctorIso j Λ).app F).symm

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- The additive graph comparison respects scalar multiplication. -/
private theorem moduleExtensionByZeroHom_smul
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
    (V : X.Etaleᵒᵖ) (r : Λ)
    (x : ((etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F).obj.obj V) :
    ((moduleExtensionByZeroUnderlyingIso j Λ F).hom.hom.app V).hom (r • x) =
      HSMul.hSMul (α := Λ) (β := ((lowerShriekModule j Λ).obj F).obj.obj V)
        (γ := ((lowerShriekModule j Λ).obj F).obj.obj V)
        r (((moduleExtensionByZeroUnderlyingIso j Λ F).hom.hom.app V).hom x) := sorry

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- The inverse additive graph comparison respects scalar multiplication. -/
private theorem moduleExtensionByZeroInv_smul
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
    (V : X.Etaleᵒᵖ) (r : Λ) (x : ((lowerShriekModule j Λ).obj F).obj.obj V) :
    ((moduleExtensionByZeroUnderlyingIso j Λ F).inv.hom.app V).hom (r • x) =
      HSMul.hSMul (α := Λ)
        (β := ((etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F).obj.obj V)
        (γ := ((etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F).obj.obj V)
        r (((moduleExtensionByZeroUnderlyingIso j Λ F).inv.hom.app V).hom x) := sorry

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- The scalar-compatible graph comparison as a module sheaf morphism. -/
private def moduleExtensionByZeroHom
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F ⟶ (lowerShriekModule j Λ).obj F :=
  liftModuleSheafHom (moduleExtensionByZeroUnderlyingIso j Λ F).hom
    (moduleExtensionByZeroHom_smul j Λ F)

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- The scalar-compatible inverse graph comparison as a module sheaf morphism. -/
private def moduleExtensionByZeroInv
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule j Λ).obj F ⟶ (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F :=
  liftModuleSheafHom (moduleExtensionByZeroUnderlyingIso j Λ F).inv
    (moduleExtensionByZeroInv_smul j Λ F)

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- The graph comparison followed by its inverse is the identity. -/
private theorem moduleExtensionByZeroHom_inv
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    moduleExtensionByZeroHom j Λ F ≫ moduleExtensionByZeroInv j Λ F = 𝟙 _ := sorry

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- The inverse graph comparison followed by the graph comparison is the identity. -/
private theorem moduleExtensionByZeroInv_hom
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    moduleExtensionByZeroInv j Λ F ≫ moduleExtensionByZeroHom j Λ F = 𝟙 _ := sorry

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- Extension by zero of a module sheaf is isomorphic to its finite-support direct image. -/
def lowerShriekModuleIsoExtensionByZero_app
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F ≅ (lowerShriekModule j Λ).obj F where
  hom := moduleExtensionByZeroHom j Λ F
  inv := moduleExtensionByZeroInv j Λ F
  hom_inv_id := moduleExtensionByZeroHom_inv j Λ F
  inv_hom_id := moduleExtensionByZeroInv_hom j Λ F

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- The module graph comparison is natural in the module sheaf. -/
private theorem moduleExtensionByZero_naturality
    {F G : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)} (f : F ⟶ G) :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).map f ≫
        (lowerShriekModuleIsoExtensionByZero_app j Λ G).hom =
      (lowerShriekModuleIsoExtensionByZero_app j Λ F).hom ≫
        (lowerShriekModule j Λ).map f := sorry

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- Étale extension by zero is naturally isomorphic to module-valued
finite-support direct image. -/
def lowerShriekModuleIsoExtensionByZero :
    etaleExtensionByZero j (ModuleCat.{u} Λ) ≅ lowerShriekModule j Λ :=
  NatIso.ofComponents (lowerShriekModuleIsoExtensionByZero_app j Λ)
    (fun f ↦ moduleExtensionByZero_naturality j Λ f)

-- Local declaration justification (metaprogramming implementation): retain private
-- comparison maps and laws in the exposed module implementation.
set_option backward.privateInPublic true in
/-- After forgetting coefficients, the forward module comparison is the composite
of coefficient comparison, the abelian graph comparison, and the inverse
finite-support coefficient comparison. -/
theorem lowerShriekModuleIsoExtensionByZero_hom_forget
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).map
        ((lowerShriekModuleIsoExtensionByZero j Λ).hom.app F) =
      ((Functor.sheafPullback.compSheafComposeIso
        (etaleRestriction j) (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
        U.smallEtaleTopology X.smallEtaleTopology).app F).hom ≫
      ((extensionByZeroIsoLowerShriek j).app
        ((sheafCompose U.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
      ((lowerShriekModule_forgetFunctorIso j Λ).app F).inv := sorry

end AlgebraicGeometry.Scheme.Etale

end
