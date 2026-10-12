/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction

/-!
# Explicit-cleavage indexed fiber actions

This module gives the choice-free indexed-functor action of a cartesian based
functor on the pseudofunctors associated to specified source and target
cleavages.  The selected-cleavage and fibred-category specializations live in
separate modules.
-/

@[expose] public section

universe uC vC uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace CartesianBasedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- Naturality of the fiber action of a cartesian based functor, oriented from source
reindexing to target reindexing. -/
noncomputable def Indexed.explicit.naturalityIso
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) :
    (χ₁.toPseudofunctor.map f.op.toLoc).toFunctor ⋙
        F.fiberFunctor V ≅
      F.fiberFunctor U ⋙
        (χ₂.toPseudofunctor.map ((𝟭 C).map f).op.toLoc).toFunctor :=
  (Reindex.natIso F χ₁ χ₂ f).symm

/-- Identity coherence for the indexed fiber action of a cartesian based functor. -/
theorem Indexed.explicit.naturalityIso.id.hom
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (U : C) (x : p₁.Fiber U) :
    (F.fiberFunctor U).map
          ((χ₁.toPseudofunctor.mapIdOp U).inv.toNatTrans.app x) ≫
        (Indexed.explicit.naturalityIso F χ₁ χ₂ (𝟙 U)).hom.app x =
      (χ₂.toPseudofunctor.mapIdOp'
        ((𝟭 C).obj U) ((𝟭 C).map (𝟙 U))
        ((𝟭 C).map_id U)).inv.toNatTrans.app
          ((F.fiberFunctor U).obj x) := sorry

/-- Inverse identity coherence for the indexed fiber action of a cartesian based functor. -/
theorem Indexed.explicit.naturalityIso.id.inv
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (U : C) (x : p₁.Fiber U) :
    (Indexed.explicit.naturalityIso F χ₁ χ₂ (𝟙 U)).inv.app x ≫
        (F.fiberFunctor U).map
          ((χ₁.toPseudofunctor.mapIdOp U).hom.toNatTrans.app x) =
      (χ₂.toPseudofunctor.mapIdOp'
        ((𝟭 C).obj U) ((𝟭 C).map (𝟙 U))
        ((𝟭 C).map_id U)).hom.toNatTrans.app
          ((F.fiberFunctor U).obj x) := sorry

/-- Composition coherence for the indexed fiber action of a cartesian based functor. -/
theorem Indexed.explicit.naturalityIso.comp.hom
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p₁.Fiber U) :
    (Indexed.explicit.naturalityIso F χ₁ χ₂ (g ≫ f)).hom.app x ≫
        (χ₂.toPseudofunctor.mapCompOp'
          ((𝟭 C).map f) ((𝟭 C).map g) ((𝟭 C).map (g ≫ f))
          ((𝟭 C).map_comp g f).symm).hom.toNatTrans.app
            ((F.fiberFunctor U).obj x) =
      (F.fiberFunctor W).map
          ((χ₁.toPseudofunctor.mapCompOp f g).hom.toNatTrans.app x) ≫
        (Indexed.explicit.naturalityIso F χ₁ χ₂ g).hom.app
          ((χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.obj x) ≫
        (χ₂.toPseudofunctor.map ((𝟭 C).map g).op.toLoc).toFunctor.map
          ((Indexed.explicit.naturalityIso F χ₁ χ₂ f).hom.app x) := sorry

/-- Inverse composition coherence for the indexed fiber action of a cartesian based functor. -/
theorem Indexed.explicit.naturalityIso.comp.inv
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p₁.Fiber U) :
    (χ₂.toPseudofunctor.map ((𝟭 C).map g).op.toLoc).toFunctor.map
          ((Indexed.explicit.naturalityIso F χ₁ χ₂ f).inv.app x) ≫
        (Indexed.explicit.naturalityIso F χ₁ χ₂ g).inv.app
          ((χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.obj x) ≫
        (F.fiberFunctor W).map
          ((χ₁.toPseudofunctor.mapCompOp f g).inv.toNatTrans.app x) =
      (χ₂.toPseudofunctor.mapCompOp'
          ((𝟭 C).map f) ((𝟭 C).map g) ((𝟭 C).map (g ≫ f))
          ((𝟭 C).map_comp g f).symm).inv.toNatTrans.app
            ((F.fiberFunctor U).obj x) ≫
        (Indexed.explicit.naturalityIso F χ₁ χ₂ (g ≫ f)).inv.app x := sorry

/-- The coherent indexed functor on fibers induced by a cartesian functor over a common base. -/
noncomputable def Indexed.explicit.functor
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      χ₁.toPseudofunctor χ₂.toPseudofunctor where
  app U := F.fiberFunctor U
  naturality f := Indexed.explicit.naturalityIso F χ₁ χ₂ f
  naturality_id U x := Indexed.explicit.naturalityIso.id.hom F χ₁ χ₂ U x
  naturality_comp f g x := Indexed.explicit.naturalityIso.comp.hom F χ₁ χ₂ f g x

/-- Components of the indexed fiber action are the ordinary induced fiber functors. -/
@[simp]
theorem Indexed.explicit.functor.app
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) (U : C) :
    (Indexed.explicit.functor F χ₁ χ₂).app U = F.fiberFunctor U := sorry

/-- Naturality of the indexed fiber action is the inverse-oriented cartesian reindexing
comparison. -/
@[simp]
theorem Indexed.explicit.functor.naturality
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) :
    (Indexed.explicit.functor F χ₁ χ₂).naturality f =
      (Reindex.natIso F χ₁ χ₂ f).symm := sorry

/-- Forward naturality components are inverse cartesian reindexing comparisons. -/
@[simp]
theorem Indexed.explicit.functor.naturality.hom.app
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    ((Indexed.explicit.functor F χ₁ χ₂).naturality f).hom.app x =
      (Reindex.mapIso F χ₁ χ₂ f x).inv := sorry

/-- Inverse naturality components are forward cartesian reindexing comparisons. -/
@[simp]
theorem Indexed.explicit.functor.naturality.inv.app
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    ((Indexed.explicit.functor F χ₁ χ₂).naturality f).inv.app x =
      (Reindex.mapIso F χ₁ χ₂ f x).hom := sorry

/-- Restricted-morphism transport through the indexed fiber action is the canonical
reindexing-conjugation formula. -/
@[simp]
theorem Indexed.explicit.functor.mapHom
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : p₁.Fiber U₁} {y : p₁.Fiber U₂}
    (φ :
      (χ₁.toPseudofunctor.map f₁.op.toLoc).toFunctor.obj x ⟶
        (χ₁.toPseudofunctor.map f₂.op.toLoc).toFunctor.obj y) :
    (Indexed.explicit.functor F χ₁ χ₂).mapHom f₁ f₂ φ =
      (Reindex.mapIso F χ₁ χ₂ f₁ x).hom ≫
        (F.fiberFunctor V).map φ ≫
        (Reindex.mapIso F χ₁ χ₂ f₂ y).inv := sorry

/-- Total-category readout of restricted-morphism transport through the explicit indexed fiber
action. -/
theorem Indexed.explicit.functor.mapHom.toTotal
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : p₁.Fiber U₁} {y : p₁.Fiber U₂}
    (φ :
      (χ₁.toPseudofunctor.map f₁.op.toLoc).toFunctor.obj x ⟶
        (χ₁.toPseudofunctor.map f₂.op.toLoc).toFunctor.obj y) :
    ((Indexed.explicit.functor F χ₁ χ₂).mapHom f₁ f₂ φ).1 =
      (Reindex.mapIso F χ₁ χ₂ f₁ x).hom.1 ≫
        ((F.fiberFunctor V).map φ).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f₂ y).inv.1 := sorry

/-- The indexed fiber action of the identity cartesian based functor is the identity indexed
functor. -/
@[simp]
theorem Indexed.explicit.functor.id
    (χ : p₁.Cleavage) :
    Indexed.explicit.functor (CartesianBasedFunctor.id p₁) χ χ =
      Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.id
        χ.toPseudofunctor := sorry

/-- The indexed fiber action of a composite cartesian based functor is the composite of the
indexed fiber actions of its factors. -/
@[simp]
theorem Indexed.explicit.functor.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂)
    (G : CartesianBasedFunctor p₂ p₃)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) (χ₃ : p₃.Cleavage) :
    Indexed.explicit.functor (F.comp G) χ₁ χ₃ =
      (Indexed.explicit.functor F χ₁ χ₂).comp
        (Indexed.explicit.functor G χ₂ χ₃) := sorry

/-- Fiberwise fully faithful component functors make the indexed fiber action fiberwise fully
faithful. -/
theorem Indexed.explicit.functor.fiberwiseFullyFaithful
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful) :
    (Indexed.explicit.functor F χ₁ χ₂).FiberwiseFullyFaithful := sorry

/-- Equivalences on all fibers make the explicit-cleavage indexed fiber action a fiberwise
equivalence. -/
theorem Indexed.explicit.functor.fiberwiseEquivalence
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (h : ∀ U : C, (F.fiberFunctor U).IsEquivalence) :
    (Indexed.explicit.functor F χ₁ χ₂).FiberwiseEquivalence := sorry

/-- A possibly universe-changing equivalence over the base induces a fiberwise-equivalence
indexed functor. -/
instance Indexed.explicit.functor.fiberwiseEquivalence.ofBasedEquivalence
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    [F.toBasedFunctor.IsEquivalence] :
    (Indexed.explicit.functor F χ₁ χ₂).FiberwiseEquivalence := sorry

end CartesianBasedFunctor

end CategoryTheory
