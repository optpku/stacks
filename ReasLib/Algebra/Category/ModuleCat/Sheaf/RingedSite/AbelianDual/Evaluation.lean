/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Generator.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Evaluation into an abelian bidual

This file constructs the canonical map from a module sheaf to its double abelian dual. The
construction is explicit on every slice site: a section `x` is sent to the functional which
evaluates `q` on the restriction of `x`. It also isolates the exact separation hypothesis needed
for these evaluation maps to be monomorphisms.

As in `AbelianDual.Functor`, the coefficient sheaf may live in an independent universe, while
modules and the dual target live in a universe containing the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.AbelianDual

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{max u v z}]
variable (O : Sheaf J CommRingCat.{w})

/-- Double abelian dualization as a covariant endofunctor of module sheaves. -/
@[stacks 01DS "abelian bidual functor"]
abbrev bidualFunctor
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) :
    ringedSiteModuleCategory.{u, v, max u v z, w} J O ⥤
      ringedSiteModuleCategory.{u, v, max u v z, w} J O :=
  (functor O 𝒥).rightOp ⋙ functor O 𝒥

/-- The double abelian dual of a module sheaf. -/
abbrev bidual
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) :
    ringedSiteModuleCategory.{u, v, max u v z, w} J O :=
  (bidualFunctor O 𝒥).obj F

/-- A natural transformation to the bidual is the canonical evaluation when, locally,
it sends `x` to the functional `f ↦ f(x)`. -/
def IsEvaluation
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (e : 𝟭 (ringedSiteModuleCategory.{u, v, max u v z, w} J O) ⟶
      bidualFunctor O 𝒥) : Prop :=
  ∀ (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (x : F.val.obj U)
      (f : LocalHom O 𝒥 F U),
    (((e.app F).val.app U).hom x).hom.app (op (Over.mk (𝟙 U.unop))) f =
      f.hom.app (op (Over.mk (𝟙 U.unop))) x

/-- Evaluate a local functional `q` on the restriction of `x` to an object of the slice site. -/
noncomputable def evalAppFun
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (x : F.val.obj U)
    (V : (Over U.unop)ᵒᵖ) :
    ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
      ((dual O 𝒥 F).over U.unop)).obj.obj V → (𝒥.over U.unop).obj.obj V :=
  fun q ↦
    q.hom.app (op (Over.mk (𝟙 V.unop.left)))
      (F.val.map V.unop.hom.op x)

/-- Local evaluation sends the zero functional to zero. -/
@[simp]
theorem evalAppFun_zero
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (x : F.val.obj U)
    (V : (Over U.unop)ᵒᵖ) :
    evalAppFun O 𝒥 F U x V 0 = 0 := sorry

/-- Local evaluation is additive in the functional. -/
theorem evalAppFun_add
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (x : F.val.obj U)
    (V : (Over U.unop)ᵒᵖ)
    (q q' : ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
      ((dual O 𝒥 F).over U.unop)).obj.obj V) :
    evalAppFun O 𝒥 F U x V (q + q') =
      evalAppFun O 𝒥 F U x V q + evalAppFun O 𝒥 F U x V q' := sorry

/-- Evaluation at a restricted section as a morphism of abelian groups. -/
noncomputable def evalApp
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (x : F.val.obj U)
    (V : (Over U.unop)ᵒᵖ) :
    ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
      ((dual O 𝒥 F).over U.unop)).obj.obj V ⟶ (𝒥.over U.unop).obj.obj V :=
  AddCommGrpCat.ofHom
    { toFun := evalAppFun O 𝒥 F U x V
      map_zero' := evalAppFun_zero O 𝒥 F U x V
      map_add' := evalAppFun_add O 𝒥 F U x V }

/-- Evaluation at a restricted section is natural on the slice site. -/
theorem evalApp_naturality
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (x : F.val.obj U)
    {V W : (Over U.unop)ᵒᵖ} (i : V ⟶ W) :
    ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
          ((dual O 𝒥 F).over U.unop)).obj.map i ≫
        evalApp O 𝒥 F U x W =
      evalApp O 𝒥 F U x V ≫ (𝒥.over U.unop).obj.map i := sorry

/-- A section of `F` over `U` evaluates local dual sections to a section of `𝒥|U`. -/
@[stacks 01DS "local bidual evaluation"]
noncomputable def evalLocal
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (x : F.val.obj U) :
    LocalHom O 𝒥 (dual O 𝒥 F) U where
  hom :=
    { app V := evalApp O 𝒥 F U x V
      naturality := fun {_ _} i ↦ evalApp_naturality O 𝒥 F U x i }

/-- Local bidual evaluation is additive in the evaluated section. -/
theorem evalLocal_add
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (x y : F.val.obj U) :
    evalLocal O 𝒥 F U (x + y) = evalLocal O 𝒥 F U x + evalLocal O 𝒥 F U y := sorry

/-- Local bidual evaluation is linear over local sections of `O`. -/
theorem evalLocal_smul
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ)
    (r : O.obj.obj U) (x : F.val.obj U) :
    evalLocal O 𝒥 F U (r • x) = r • evalLocal O 𝒥 F U x := sorry

/-- The component on `U` of canonical evaluation into the double abelian dual. -/
@[stacks 01DS "bidual evaluation component"]
noncomputable def toBidualApp
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    F.val.obj U ⟶ (dual O 𝒥 (dual O 𝒥 F)).val.obj U :=
  ModuleCat.ofHom
    (X := F.val.obj U)
    (Y := (dual O 𝒥 (dual O 𝒥 F)).val.obj U)
    { toFun := evalLocal O 𝒥 F U
      map_add' := evalLocal_add O 𝒥 F U
      map_smul' := evalLocal_smul O 𝒥 F U }

/-- Canonical evaluation into the bidual commutes with restriction on the base site. -/
theorem toBidualApp_naturality
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) {U V : Cᵒᵖ} (i : U ⟶ V) :
    F.val.map i ≫
        (ModuleCat.restrictScalars (O.obj.map i).hom).map (toBidualApp O 𝒥 F V) =
      toBidualApp O 𝒥 F U ≫ (dual O 𝒥 (dual O 𝒥 F)).val.map i := sorry

/-- Canonical evaluation of a module sheaf into its double abelian dual. -/
@[stacks 01DS "canonical bidual evaluation"]
noncomputable def toBidual
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) : F ⟶ bidual O 𝒥 F where
  val :=
    { app U := toBidualApp O 𝒥 F U
      naturality := toBidualApp_naturality O 𝒥 F }

/-- Canonical bidual evaluation is natural in the module sheaf. -/
theorem toBidual_naturality
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    {F G : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f : F ⟶ G) :
    f ≫ toBidual O 𝒥 G =
      toBidual O 𝒥 F ≫ (bidualFunctor O 𝒥).map f := sorry

/-- Naturality of bidual evaluation in the identity-functor presentation. -/
theorem evaluation_naturality
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    {F G : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f : F ⟶ G) :
    (𝟭 (ringedSiteModuleCategory.{u, v, max u v z, w} J O)).map f ≫ toBidual O 𝒥 G =
      toBidual O 𝒥 F ≫ (bidualFunctor O 𝒥).map f := sorry

/-- Canonical bidual evaluation as a natural transformation. -/
@[stacks 01DS "canonical bidual evaluation transformation"]
noncomputable def evaluation
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) :
    𝟭 (ringedSiteModuleCategory.{u, v, max u v z, w} J O) ⟶ bidualFunctor O 𝒥 where
  app F := toBidual O 𝒥 F
  naturality := fun {_ _} f ↦ evaluation_naturality O 𝒥 f

/-- The canonical evaluation transformation satisfies the local formula `x ↦ (f ↦ f(x))`. -/
theorem evaluation_isEvaluation
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) :
    IsEvaluation O 𝒥 (evaluation O 𝒥) := sorry

/-- The abelian sheaf `𝒥` separates module maps when local maps into `𝒥` detect equality. -/
@[stacks 01DS "abelian dual separates module maps"]
def Separates
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) : Prop :=
  ∀ {F G : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f g : F ⟶ G),
    (∀ (U : Cᵒᵖ) (q : LocalHom O 𝒥 G U),
      preFun O 𝒥 f U q = preFun O 𝒥 g U q) → f = g

/-- A coseparator among abelian sheaves separates the underlying maps of module sheaves. -/
theorem separates_of_isCoseparator
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) (h𝒥 : IsCoseparator 𝒥) :
    Separates O 𝒥 := sorry

/-- If `𝒥` separates module maps, every component of canonical bidual evaluation is monic. -/
@[stacks 01DS]
theorem mono_toBidual
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (h𝒥 : Separates O 𝒥) (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) :
    Mono (toBidual O 𝒥 F) := sorry

/-- Evaluation into the bidual defined by a coseparator is monic. -/
@[stacks 01DS "coseparator form"]
theorem mono_toBidual_of_isCoseparator
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) (h𝒥 : IsCoseparator 𝒥)
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) :
    Mono (toBidual O 𝒥 F) := sorry

end SheafOfModules.RingedSite.AbelianDual
