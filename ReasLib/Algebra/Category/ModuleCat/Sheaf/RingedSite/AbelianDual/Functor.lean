/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Opposite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul
import Mathlib.Tactic.CrossRefAttribute

/-!
# The abelian-sheaf-valued dual functor

Let `O` be a sheaf of commutative rings and let `𝒥` be a sheaf of abelian groups. The
abelian dual of an `O`-module sheaf `F` is the sheaf
`U ↦ Hom(F|U, 𝒥|U)` of morphisms of underlying abelian sheaves. Its `O(U)`-module
structure is induced by precomposition with the action of local sections on `F|U`.

This construction is separate from the internal Hom of two `O`-module sheaves: the target
`𝒥` need not carry an `O`-module structure.

The coefficient sheaf `O` may live in an independent universe. Module sheaves and the dual
target live in `max u v z`, which contains the object and morphism universes of the site and a
chosen target universe `z`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.AbelianDual

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{max u v z}]
variable (O : Sheaf J CommRingCat.{w})

/-- The underlying abelian sheaf of a module sheaf on a ringed site. -/
noncomputable abbrev underlying :
    ringedSiteModuleCategory.{u, v, max u v z, w} J O ⥤ Sheaf J AddCommGrpCat.{max u v z} :=
  SheafOfModules.toSheaf (ringSheaf J O)

/-- Local abelian-sheaf morphisms from the restriction of `F` to the restriction of `𝒥`. -/
@[stacks 01DR "local abelian dual"]
def LocalHom (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :=
  (SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj (F.over U.unop) ⟶
    𝒥.over U.unop

namespace LocalHom

/-- Local abelian duals inherit the additive group structure on morphisms of abelian sheaves. -/
@[implicit_reducible]
noncomputable instance instAddCommGroup
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    AddCommGroup (LocalHom O 𝒥 F U) :=
  inferInstanceAs (AddCommGroup
    ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj (F.over U.unop) ⟶
      𝒥.over U.unop))

/-- Endomorphisms of the source act on local abelian duals by precomposition. -/
@[implicit_reducible]
noncomputable instance instModuleEnd
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    Module
      (End ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
        (F.over U.unop)))ᵐᵒᵖ
      (LocalHom O 𝒥 F U) :=
  inferInstanceAs (Module
    (End ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
      (F.over U.unop)))ᵐᵒᵖ
    (((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
      (F.over U.unop)) ⟶ 𝒥.over U.unop))

end LocalHom

/-- Multiplication by a local section on the underlying abelian sheaf of `F|U`. -/
noncomputable def actionHom
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (r : O.obj.obj U) :
    End ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
      (F.over U.unop)) :=
  (SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).map
    (SheafOfModules.sectionActionHom O F U.unop r)

/-- The zero local section acts by the zero endomorphism on the underlying abelian sheaf. -/
@[simp]
theorem actionHom_zero
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    actionHom O F U 0 = 0 := sorry

/-- The action on the underlying abelian sheaf is additive in the local section. -/
theorem actionHom_add
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (r s : O.obj.obj U) :
    actionHom O F U (r + s) = actionHom O F U r + actionHom O F U s := sorry

/-- The unit local section acts by the identity on the underlying abelian sheaf. -/
@[simp]
theorem actionHom_one
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    actionHom O F U 1 = 𝟙 _ := sorry

/-- Multiplication of local sections agrees with multiplication in the endomorphism ring. -/
theorem actionHom_mul
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (r s : O.obj.obj U) :
    actionHom O F U (r * s) = actionHom O F U r * actionHom O F U s := sorry

/-- The local-section action on the underlying abelian sheaf as a ring homomorphism. -/
noncomputable def action
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    O.obj.obj U →+*
      End ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
        (F.over U.unop)) where
  toFun := actionHom O F U
  map_one' := actionHom_one O F U
  map_zero' := actionHom_zero O F U
  map_mul' := actionHom_mul O F U
  map_add' := actionHom_add O F U

/-- Images of local sections commute in the endomorphism ring of the underlying abelian sheaf. -/
theorem action_commute
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) (r s : O.obj.obj U) :
    Commute (action O F U r) (action O F U s) := sorry

/-- The source action, with variance reversed for its precomposition action on local Homs. -/
noncomputable def actionOp
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    O.obj.obj U →+*
      (End ((SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).obj
        (F.over U.unop)))ᵐᵒᵖ :=
  (action O F U).toOpposite (action_commute O F U)

/-- The canonical local `O(U)`-module structure on abelian-sheaf morphisms `F|U ⟶ 𝒥|U`. -/
@[stacks 01DR "precomposition module structure", implicit_reducible]
noncomputable instance homModule
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    Module (O.obj.obj U) (LocalHom O 𝒥 F U) :=
  Module.compHom _ (actionOp O F U)

/-- Scalar multiplication on a local abelian dual is precomposition by the source action. -/
@[simp, stacks 01DR "precomposition action"]
theorem smul_eq_comp
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ)
    (r : O.obj.obj U) (f : LocalHom O 𝒥 F U) :
    r • f = actionHom O F U r ≫ f := sorry

/-- Restrict a local abelian dual along a morphism in the base site. -/
@[stacks 01DR "restriction of local abelian duals"]
noncomputable def restrictFun
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) {U V : Cᵒᵖ} (i : U ⟶ V) :
    LocalHom O 𝒥 F U → LocalHom O 𝒥 F V :=
  fun f ↦
    (SheafOfModules.toSheaf ((ringSheaf J O).over V.unop)).map
        ((SheafOfModules.overFunctorMap (ringSheaf J O) i.unop).inv.app F) ≫
      (J.overMapPullback AddCommGrpCat.{max u v z} i.unop).map f ≫
        (Sheaf.pushforwardOverMapIso 𝒥 i.unop).hom

/-- Restriction of local abelian duals preserves addition. -/
theorem restrictFun_add
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) {U V : Cᵒᵖ} (i : U ⟶ V)
    (f g : LocalHom O 𝒥 F U) :
    restrictFun O 𝒥 F i (f + g) =
      restrictFun O 𝒥 F i f + restrictFun O 𝒥 F i g := sorry

/-- Restriction of local abelian duals is semilinear over restriction of local sections. -/
theorem restrictFun_smul
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) {U V : Cᵒᵖ} (i : U ⟶ V)
    (r : O.obj.obj U) (f : LocalHom O 𝒥 F U) :
    restrictFun O 𝒥 F i (r • f) = O.obj.map i r • restrictFun O 𝒥 F i f := sorry

/-- The semilinear restriction map on modules of local abelian duals. -/
@[stacks 01DR "linear restriction of local abelian duals"]
noncomputable def restrict
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) {U V : Cᵒᵖ} (i : U ⟶ V) :
    ModuleCat.of (O.obj.obj U) (LocalHom O 𝒥 F U) ⟶
      (ModuleCat.restrictScalars (O.obj.map i).hom).obj
        (ModuleCat.of (O.obj.obj V) (LocalHom O 𝒥 F V)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (O.obj.obj U) (LocalHom O 𝒥 F U))
    (Y := (ModuleCat.restrictScalars (O.obj.map i).hom).obj
      (ModuleCat.of (O.obj.obj V) (LocalHom O 𝒥 F V)))
    { toFun := restrictFun O 𝒥 F i
      map_add' := restrictFun_add O 𝒥 F i
      map_smul' := restrictFun_smul O 𝒥 F i }

/-- Bundled restriction evaluates to restriction of the underlying local morphism. -/
@[simp]
theorem restrict_apply
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) {U V : Cᵒᵖ} (i : U ⟶ V)
    (f : LocalHom O 𝒥 F U) :
    (restrict O 𝒥 F i).hom f = restrictFun O 𝒥 F i f := sorry

/-- Restriction of local abelian duals respects identity arrows. -/
theorem restrict_id
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    restrict O 𝒥 F (𝟙 U) =
      (ModuleCat.restrictScalarsId' (O.obj.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (O.obj.map_id U))).inv.app _ := sorry

/-- Restriction of local abelian duals respects composition. -/
theorem restrict_comp
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) {U V W : Cᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    restrict O 𝒥 F (i ≫ j) =
      restrict O 𝒥 F i ≫
        (ModuleCat.restrictScalars (O.obj.map i).hom).map (restrict O 𝒥 F j) ≫
          (ModuleCat.restrictScalarsComp' (O.obj.map i).hom (O.obj.map j).hom
            (O.obj.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom (O.obj.map_comp i j))).inv.app _ := sorry

/-- The presheaf of `O`-modules of local abelian duals of `F` with values in `𝒥`. -/
@[stacks 01DR "abelian dual presheaf"]
noncomputable def presheaf
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) :
    PresheafOfModules (ringSheaf J O).obj where
  obj U := ModuleCat.of (O.obj.obj U) (LocalHom O 𝒥 F U)
  map i := restrict O 𝒥 F i
  map_id := restrict_id O 𝒥 F
  map_comp := restrict_comp O 𝒥 F

/-- The local-abelian-dual presheaf satisfies the sheaf condition. -/
theorem presheaf_isSheaf
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) :
    Presheaf.IsSheaf J (presheaf O 𝒥 F).presheaf := sorry

/-- The `O`-module sheaf `Hom_Ab(F, 𝒥)`, with scalars acting by precomposition on `F`. -/
@[stacks 01DR "abelian-sheaf-valued dual"]
noncomputable def dual
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) :
    ringedSiteModuleCategory.{u, v, max u v z, w} J O where
  val := presheaf O 𝒥 F
  isSheaf := presheaf_isSheaf O 𝒥 F

/-- Sections of `dual O 𝒥 F` over `U` are local morphisms of underlying abelian sheaves. -/
theorem dual_val_obj
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) (U : Cᵒᵖ) :
    (dual O 𝒥 F).val.obj U = ModuleCat.of (O.obj.obj U) (LocalHom O 𝒥 F U) := sorry

/-- Precompose a local abelian dual with the restriction of a module-sheaf morphism. -/
noncomputable def preFun
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    {F G : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f : F ⟶ G) (U : Cᵒᵖ) :
    LocalHom O 𝒥 G U → LocalHom O 𝒥 F U :=
  fun g ↦
    (SheafOfModules.toSheaf ((ringSheaf J O).over U.unop)).map (f.over U.unop) ≫ g

/-- Precomposition of local abelian duals preserves addition. -/
theorem preFun_add
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    {F G : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f : F ⟶ G) (U : Cᵒᵖ)
    (g h : LocalHom O 𝒥 G U) :
    preFun O 𝒥 f U (g + h) = preFun O 𝒥 f U g + preFun O 𝒥 f U h := sorry

/-- Precomposition of local abelian duals is linear over local sections. -/
theorem preFun_smul
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    {F G : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f : F ⟶ G) (U : Cᵒᵖ)
    (r : O.obj.obj U) (g : LocalHom O 𝒥 G U) :
    preFun O 𝒥 f U (r • g) = r • preFun O 𝒥 f U g := sorry

/-- The linear map on local abelian duals induced by precomposition. -/
noncomputable def pre
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    {F G : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f : F ⟶ G) (U : Cᵒᵖ) :
    (presheaf O 𝒥 G).obj U ⟶ (presheaf O 𝒥 F).obj U :=
  ModuleCat.ofHom
    { toFun := preFun O 𝒥 f U
      map_add' := preFun_add O 𝒥 f U
      map_smul' := preFun_smul O 𝒥 f U }

/-- Precomposition commutes with restriction of local abelian duals. -/
theorem pre_naturality
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    {F G : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f : F ⟶ G)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (presheaf O 𝒥 G).map i ≫
        (ModuleCat.restrictScalars (O.obj.map i).hom).map (pre O 𝒥 f V) =
      pre O 𝒥 f U ≫ (presheaf O 𝒥 F).map i := sorry

/-- A module-sheaf morphism induces a reversed morphism of abelian-sheaf-valued duals. -/
noncomputable def map
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    {F G : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f : F ⟶ G) :
    dual O 𝒥 G ⟶ dual O 𝒥 F where
  val :=
    { app U := pre O 𝒥 f U
      naturality := pre_naturality O 𝒥 f }

/-- Dualization by precomposition preserves identity morphisms. -/
theorem map_id
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    (F : ringedSiteModuleCategory.{u, v, max u v z, w} J O) :
    map O 𝒥 (𝟙 F) = 𝟙 (dual O 𝒥 F) := sorry

/-- Dualization reverses composition. -/
theorem map_comp
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
    {F G H : ringedSiteModuleCategory.{u, v, max u v z, w} J O} (f : F ⟶ G) (g : G ⟶ H) :
    map O 𝒥 (f ≫ g) = map O 𝒥 g ≫ map O 𝒥 f := sorry

/-- Contravariant abelian-sheaf-valued dualization of module sheaves. -/
@[stacks 01DR "abelian dual functor"]
noncomputable def functor
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) :
    (ringedSiteModuleCategory.{u, v, max u v z, w} J O)ᵒᵖ ⥤
      ringedSiteModuleCategory.{u, v, max u v z, w} J O where
  obj F := dual O 𝒥 F.unop
  map f := map O 𝒥 f.unop
  map_id := fun F ↦ map_id O 𝒥 F.unop
  map_comp := fun f g ↦ map_comp O 𝒥 g.unop f.unop

/-- Abelian dualization is additive. -/
noncomputable instance functor_additive
    (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) :
    (functor O 𝒥).Additive := sorry

end SheafOfModules.RingedSite.AbelianDual
