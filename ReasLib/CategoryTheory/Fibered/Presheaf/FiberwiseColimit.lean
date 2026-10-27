/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf
public import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiberwise colimits of presheaves

This leaf owns the topology-independent presheaf obtained by taking a colimit over each fiber of a
fibered category.  Sheafification and lower-shriek identifications belong to higher layers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v wX vX a b

namespace CategoryTheory.FiberedCategoryOver.Presheaf

variable {C : Type u} [Category.{v} C]
variable (X : FiberedCategoryOver.{u, v, wX, vX} C)
variable (A : Type a) [Category.{b} A]

/-- The colimit of the restriction of a presheaf to the fiber over `V`. -/
@[stacks 08PI "fiberwise colimit object"]
noncomputable def fiberwiseColimitObj
    (F : X.totalᵒᵖ ⥤ A) (V : Cᵒᵖ)
    [HasColimitsOfShape (X.p.Fiber V.unop)ᵒᵖ A] : A :=
  colimit (restrict X A F V.unop)

/-- The leg into the target-fiber colimit induced by a cartesian lift over `f : V ⟶ U`. -/
@[stacks 08PI "fiberwise colimit cocone leg"]
noncomputable def fiberwiseColimitCoconeApp
    (F : X.totalᵒᵖ ⥤ A)
    {U V : C} (f : V ⟶ U) (x : (X.p.Fiber U)ᵒᵖ)
    [HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    (restrict X A F U).obj x ⟶ fiberwiseColimitObj X A F (op V) :=
  cartesianRestrictionApp X A F f x ≫
    colimit.ι (restrict X A F V)
      (((Functor.Cleavage.ofIsFibered X.p).reindex f).op.obj x)

/-- Naturality of the legs in the source fiber. -/
@[stacks 08PI "fiberwise colimit cocone naturality"]
theorem fiberwiseColimitCocone_naturality
    (F : X.totalᵒᵖ ⥤ A) {U V : C} (f : V ⟶ U)
    [HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    ∀ {x y : (X.p.Fiber U)ᵒᵖ} (g : x ⟶ y),
      (restrict X A F U).map g ≫
          fiberwiseColimitCoconeApp X A F f y =
        fiberwiseColimitCoconeApp X A F f x ≫ 𝟙 _ := by
  intro x y g
  rw [Category.comp_id, fiberwiseColimitCoconeApp, fiberwiseColimitCoconeApp,
    ← Category.assoc, cartesianRestriction_naturality X A F f g, Category.assoc]
  exact congrArg (fun k => cartesianRestrictionApp X A F f x ≫ k)
    (colimit.w (restrict X A F V)
      (((Functor.Cleavage.ofIsFibered X.p).reindex f).op.map g))

/-- The simplified form of fiberwise-colimit cocone naturality. -/
@[stacks 08PI "fiberwise colimit cocone naturality simplified"]
theorem fiberwiseColimitCocone_naturality_eq
    (F : X.totalᵒᵖ ⥤ A) {U V : C} (f : V ⟶ U)
    [HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    ∀ {x y : (X.p.Fiber U)ᵒᵖ} (g : x ⟶ y),
      (restrict X A F U).map g ≫
          fiberwiseColimitCoconeApp X A F f y =
        fiberwiseColimitCoconeApp X A F f x := by
  intro x y g
  simpa only [Category.comp_id] using fiberwiseColimitCocone_naturality X A F f g

/-- The cocone over the source-fiber restriction with vertex the target-fiber colimit. -/
@[stacks 08PI "fiberwise colimit restriction cocone"]
noncomputable def fiberwiseColimitCocone
    (F : X.totalᵒᵖ ⥤ A) {U V : C} (f : V ⟶ U)
    [HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    Cocone (restrict X A F U) where
  pt := fiberwiseColimitObj X A F (op V)
  ι :=
    { app := fun x => fiberwiseColimitCoconeApp X A F f x
      naturality := fun {_ _} g ↦ fiberwiseColimitCocone_naturality X A F f g }

/-- The restriction map on fiberwise colimits induced by a base arrow. -/
@[stacks 08PI "fiberwise colimit map"]
noncomputable def fiberwiseColimitMap
    (F : X.totalᵒᵖ ⥤ A) {U V : Cᵒᵖ} (f : U ⟶ V)
    [HasColimitsOfShape (X.p.Fiber U.unop)ᵒᵖ A]
    [HasColimitsOfShape (X.p.Fiber V.unop)ᵒᵖ A] :
    fiberwiseColimitObj X A F U ⟶ fiberwiseColimitObj X A F V :=
  colimit.desc (restrict X A F U.unop)
    (fiberwiseColimitCocone X A F f.unop)

/-- Identity law for the fiberwise-colimit restriction maps. -/
@[simp, stacks 08PI "fiberwise colimit identity map"]
theorem fiberwiseColimitMap_id
    (F : X.totalᵒᵖ ⥤ A) (U : Cᵒᵖ)
    [HasColimitsOfShape (X.p.Fiber U.unop)ᵒᵖ A] :
    fiberwiseColimitMap X A F (𝟙 U) =
      𝟙 (fiberwiseColimitObj X A F U) := by
  dsimp only [fiberwiseColimitMap, fiberwiseColimitCocone,
    fiberwiseColimitCoconeApp, fiberwiseColimitObj]
  apply colimit.hom_ext
  intro x
  simp only [colimit.ι_desc, Category.comp_id]
  change F.map ((Functor.Cleavage.ofIsFibered X.p).cartesianHom
      (𝟙 U.unop) x.unop).op ≫ _ = _
  rw [← Functor.Cleavage.Reindex.idIsoApp.inv.eq_cartesianHom]
  exact colimit.w (restrict X A F U.unop)
    (Functor.Cleavage.Reindex.idIsoApp
      (Functor.Cleavage.ofIsFibered X.p) U.unop x.unop).inv.op

set_option backward.isDefEq.respectTransparency false in
/-- Composition law for the fiberwise-colimit restriction maps. -/
@[simp, stacks 08PI "fiberwise colimit composition map"]
theorem fiberwiseColimitMap_comp
    (F : X.totalᵒᵖ ⥤ A) {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    [HasColimitsOfShape (X.p.Fiber U.unop)ᵒᵖ A]
    [HasColimitsOfShape (X.p.Fiber V.unop)ᵒᵖ A]
    [HasColimitsOfShape (X.p.Fiber W.unop)ᵒᵖ A] :
    fiberwiseColimitMap X A F (f ≫ g) =
      fiberwiseColimitMap X A F f ≫ fiberwiseColimitMap X A F g := by
  dsimp only [fiberwiseColimitMap, fiberwiseColimitCocone,
    fiberwiseColimitCoconeApp, fiberwiseColimitObj]
  apply colimit.hom_ext
  intro x
  simp only [colimit.ι_desc_assoc, colimit.ι_desc, Category.assoc]
  let χ := Functor.Cleavage.ofIsFibered X.p
  let e := Functor.Cleavage.Reindex.compIsoApp χ f.unop g.unop x.unop
  have h := colimit.w (restrict X A F W.unop) e.inv.op
  change F.map e.inv.1.op ≫ colimit.ι (restrict X A F W.unop)
      (op (χ.reindexObj g.unop (χ.reindexObj f.unop x.unop))) =
    colimit.ι (restrict X A F W.unop)
      (op (χ.reindexObj (g.unop ≫ f.unop) x.unop)) at h
  change F.map (χ.cartesianHom (g.unop ≫ f.unop) x.unop).op ≫
      colimit.ι (restrict X A F W.unop)
        (op (χ.reindexObj (g.unop ≫ f.unop) x.unop)) =
    F.map (χ.cartesianHom f.unop x.unop).op ≫
      F.map (χ.cartesianHom g.unop (χ.reindexObj f.unop x.unop)).op ≫
        colimit.ι (restrict X A F W.unop)
          (op (χ.reindexObj g.unop (χ.reindexObj f.unop x.unop)))
  rw [← h, ← Category.assoc, ← F.map_comp, ← op_comp,
    Functor.Cleavage.Reindex.compIsoApp.inv.fac, op_comp, F.map_comp,
    Category.assoc]

/-- The presheaf on the base obtained by taking colimits over all fibers. -/
@[stacks 08PI "fiberwise colimit presheaf"]
noncomputable def fiberwiseColimit
    (F : X.totalᵒᵖ ⥤ A)
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] : Cᵒᵖ ⥤ A where
  obj := fun V => fiberwiseColimitObj X A F V
  map := fun {_ _} f => fiberwiseColimitMap X A F f
  map_id := fun V => fiberwiseColimitMap_id X A F V
  map_comp := fun f g => fiberwiseColimitMap_comp X A F f g

/-- Objectwise evaluation of the fiberwise-colimit presheaf. -/
@[simp, stacks 08PI "fiberwise colimit presheaf object formula"]
theorem fiberwiseColimit_obj
    (F : X.totalᵒᵖ ⥤ A) (V : Cᵒᵖ)
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    (fiberwiseColimit X A F).obj V = fiberwiseColimitObj X A F V := rfl

/-- On a colimit generator, the fiberwise-colimit map is the cartesian restriction leg followed by
the universal colimit injection in the target fiber. -/
@[simp, stacks 08PI "fiberwise colimit generator map"]
theorem fiberwiseColimit_ι_map
    (F : X.totalᵒᵖ ⥤ A) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (X.p.Fiber U.unop)ᵒᵖ)
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    colimit.ι (restrict X A F U.unop) x ≫
        (fiberwiseColimit X A F).map f =
      cartesianRestrictionApp X A F f.unop x ≫
        colimit.ι (restrict X A F V.unop)
          (((Functor.Cleavage.ofIsFibered X.p).reindex f.unop).op.obj x) := by
  exact colimit.ι_desc (fiberwiseColimitCocone X A F f.unop) x

namespace fiberwiseColimit

/-- The map on one fiberwise colimit induced by a morphism of total presheaves. -/
@[stacks 08PI "fiberwise colimit coefficient map component"]
noncomputable def mapApp
    {F G : X.totalᵒᵖ ⥤ A} (τ : F ⟶ G) (V : Cᵒᵖ)
    [HasColimitsOfShape (X.p.Fiber V.unop)ᵒᵖ A] :
    fiberwiseColimitObj X A F V ⟶ fiberwiseColimitObj X A G V :=
  colimMap (restrictMap X A τ V.unop)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the fiberwise-colimit coefficient map in the base category. -/
@[stacks 08PI "fiberwise colimit coefficient map naturality"]
theorem map_naturality
    {F G : X.totalᵒᵖ ⥤ A} (τ : F ⟶ G)
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A]
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (fiberwiseColimit X A F).map f ≫ mapApp X A τ V =
      mapApp X A τ U ≫ (fiberwiseColimit X A G).map f := by
  dsimp only [fiberwiseColimit, fiberwiseColimitMap, mapApp,
    fiberwiseColimitCocone, fiberwiseColimitCoconeApp, fiberwiseColimitObj]
  apply colimit.hom_ext
  intro x
  simp only [Category.assoc, colimit.ι_desc_assoc, colimit.ι_desc,
    ι_colimMap_assoc, ι_colimMap]
  change F.map ((Functor.Cleavage.ofIsFibered X.p).cartesianHom
      f.unop x.unop).op ≫ τ.app _ ≫ _ =
    τ.app _ ≫ G.map ((Functor.Cleavage.ofIsFibered X.p).cartesianHom
      f.unop x.unop).op ≫ _
  rw [← Category.assoc, τ.naturality, Category.assoc]

/-- The map of fiberwise-colimit presheaves induced by a coefficient morphism. -/
@[stacks 08PI "fiberwise colimit coefficient map"]
noncomputable def map
    {F G : X.totalᵒᵖ ⥤ A} (τ : F ⟶ G)
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    fiberwiseColimit X A F ⟶ fiberwiseColimit X A G where
  app := fun V => mapApp X A τ V
  naturality := fun {_ _} f ↦ map_naturality X A τ f

/-- Fiberwise-colimit coefficient maps preserve identities. -/
@[simp, stacks 08PI "fiberwise colimit coefficient identity"]
theorem map_id
    (F : X.totalᵒᵖ ⥤ A)
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    map X A (𝟙 F) = 𝟙 (fiberwiseColimit X A F) := by
  ext V
  change colim.map (𝟙 (restrict X A F V.unop)) =
    𝟙 (colim.obj (restrict X A F V.unop))
  exact Functor.map_id colim (restrict X A F V.unop)

/-- Fiberwise-colimit coefficient maps preserve composition. -/
@[simp, stacks 08PI "fiberwise colimit coefficient composition"]
theorem map_comp
    {F G H : X.totalᵒᵖ ⥤ A} (τ : F ⟶ G) (σ : G ⟶ H)
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    map X A (τ ≫ σ) = map X A τ ≫ map X A σ := by
  ext V
  change colim.map (restrictMap X A (τ ≫ σ) V.unop) =
    colim.map (restrictMap X A τ V.unop) ≫ colim.map (restrictMap X A σ V.unop)
  simp only [restrictMap, Functor.whiskerLeft_comp, Functor.map_comp]

/-- Fiberwise colimit as a functor from total presheaves to base presheaves. -/
@[stacks 08PI "fiberwise colimit coefficient functor"]
noncomputable def functor
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A] :
    (X.totalᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) where
  obj F := fiberwiseColimit X A F
  map τ := map X A τ
  map_id F := map_id X A F
  map_comp τ σ := map_comp X A τ σ

/-- Evaluation of the fiberwise-colimit coefficient functor on objects. -/
@[simp, stacks 08PI "fiberwise colimit coefficient functor object formula"]
theorem functor_obj
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A]
    (F : X.totalᵒᵖ ⥤ A) :
    (functor X A).obj F = fiberwiseColimit X A F := rfl

/-- Evaluation of the fiberwise-colimit coefficient functor on morphisms. -/
@[simp, stacks 08PI "fiberwise colimit coefficient functor map formula"]
theorem functor_map
    [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A]
    {F G : X.totalᵒᵖ ⥤ A} (τ : F ⟶ G) :
    (functor X A).map τ = map X A τ := rfl

end fiberwiseColimit

end CategoryTheory.FiberedCategoryOver.Presheaf
