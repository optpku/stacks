module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor

/-!
# Selected-cleavage indexed fiber actions

This module specializes the explicit-cleavage indexed action to the cleavages
selected from fibred projections. It also records the fixed-owner
equivalence instances for this specialization.
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

/-- The indexed fiber action specialized to the cleavages selected from fibred source and target
projections. The choice-explicit owner is `Indexed.explicit.functor`. -/
noncomputable def Indexed.chosen.functor
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered] :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      (Functor.fiberPseudofunctor p₁) (Functor.fiberPseudofunctor p₂) :=
  Indexed.explicit.functor F
    (Functor.Cleavage.ofIsFibered p₁) (Functor.Cleavage.ofIsFibered p₂)

/-- Components of the selected indexed fiber action are the ordinary fiber functors. -/
@[simp]
theorem Indexed.chosen.functor.app
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered] (U : C) :
    (Indexed.chosen.functor F).app U = F.fiberFunctor U := sorry

/-- Naturality of the selected indexed fiber action is the selected cartesian reindexing
comparison in inverse orientation. -/
@[simp]
theorem Indexed.chosen.functor.naturality
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    {U V : C} (f : V ⟶ U) :
    (Indexed.chosen.functor F).naturality f =
      (Reindex.natIso F
        (Functor.Cleavage.ofIsFibered p₁)
        (Functor.Cleavage.ofIsFibered p₂) f).symm := sorry

/-- Forward naturality components of the selected indexed fiber action. -/
@[simp]
theorem Indexed.chosen.functor.naturality.hom.app
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    ((Indexed.chosen.functor F).naturality f).hom.app x =
      (Reindex.mapIso F
        (Functor.Cleavage.ofIsFibered p₁)
        (Functor.Cleavage.ofIsFibered p₂) f x).inv := sorry

/-- Inverse naturality components of the selected indexed fiber action. -/
@[simp]
theorem Indexed.chosen.functor.naturality.inv.app
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    ((Indexed.chosen.functor F).naturality f).inv.app x =
      (Reindex.mapIso F
        (Functor.Cleavage.ofIsFibered p₁)
        (Functor.Cleavage.ofIsFibered p₂) f x).hom := sorry

/-- Restricted-morphism transport through the selected indexed fiber action is the selected
reindexing-conjugation formula. -/
@[simp]
theorem Indexed.chosen.functor.mapHom
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : p₁.Fiber U₁} {y : p₁.Fiber U₂}
    (φ :
      ((Functor.fiberPseudofunctor p₁).map
        f₁.op.toLoc).toFunctor.obj x ⟶
      ((Functor.fiberPseudofunctor p₁).map
        f₂.op.toLoc).toFunctor.obj y) :
    (Indexed.chosen.functor F).mapHom f₁ f₂ φ =
      (Reindex.mapIso F
        (Functor.Cleavage.ofIsFibered p₁)
        (Functor.Cleavage.ofIsFibered p₂) f₁ x).hom ≫
        (F.fiberFunctor V).map φ ≫
      (Reindex.mapIso F
        (Functor.Cleavage.ofIsFibered p₁)
        (Functor.Cleavage.ofIsFibered p₂) f₂ y).inv := sorry

/-- Total-category readout of restricted-morphism transport through the selected indexed fiber
action. -/
theorem Indexed.chosen.functor.mapHom.toTotal
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : p₁.Fiber U₁} {y : p₁.Fiber U₂}
    (φ :
      ((Functor.fiberPseudofunctor p₁).map
        f₁.op.toLoc).toFunctor.obj x ⟶
      ((Functor.fiberPseudofunctor p₁).map
        f₂.op.toLoc).toFunctor.obj y) :
    ((Indexed.chosen.functor F).mapHom f₁ f₂ φ).1 =
      (Reindex.mapIso F
        (Functor.Cleavage.ofIsFibered p₁)
        (Functor.Cleavage.ofIsFibered p₂) f₁ x).hom.1 ≫
        ((F.fiberFunctor V).map φ).1 ≫
      (Reindex.mapIso F
        (Functor.Cleavage.ofIsFibered p₁)
        (Functor.Cleavage.ofIsFibered p₂) f₂ y).inv.1 := sorry

/-- The selected indexed fiber action of the identity cartesian based functor is the identity
indexed functor. -/
@[simp]
theorem Indexed.chosen.functor.id [p₁.IsFibered] :
    Indexed.chosen.functor (CartesianBasedFunctor.id p₁) =
      Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.id
        (Functor.fiberPseudofunctor p₁) := sorry

/-- The selected indexed fiber action of a composite cartesian based functor is the composite
of the selected indexed fiber actions of its factors. -/
@[simp]
theorem Indexed.chosen.functor.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂)
    (G : CartesianBasedFunctor p₂ p₃)
    [p₁.IsFibered] [p₂.IsFibered] [p₃.IsFibered] :
    Indexed.chosen.functor (F.comp G) =
      (Indexed.chosen.functor F).comp
        (Indexed.chosen.functor G) := sorry

/-- Fiberwise fully faithful selected components make the selected indexed fiber action
fiberwise fully faithful. -/
theorem Indexed.chosen.functor.fiberwiseFullyFaithful
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful) :
    (Indexed.chosen.functor F).FiberwiseFullyFaithful := sorry

/-- Equivalences on all fibers make the selected indexed fiber action a fiberwise
equivalence. -/
theorem Indexed.chosen.functor.fiberwiseEquivalence
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (h : ∀ U : C, (F.fiberFunctor U).IsEquivalence) :
    (Indexed.chosen.functor F).FiberwiseEquivalence := sorry

/-- A possibly universe-changing equivalence over the base induces a fiberwise equivalence on
the selected fiber pseudofunctors. -/
instance Indexed.chosen.functor.fiberwiseEquivalence.ofBasedEquivalence
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    [F.toBasedFunctor.IsEquivalence] :
    (Indexed.chosen.functor F).FiberwiseEquivalence := sorry

section FixedOwnerEquivalence

universe uS vS

variable {S₁ S₂ : Type uS} [Category.{vS} S₁] [Category.{vS} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- A bicategorical equivalence of based categories induces a fiberwise-equivalence indexed
functor for any explicit source and target cleavages. -/
instance Indexed.explicit.functor.fiberwiseEquivalence.ofEquivalence
    (e : BasedCategory.ofFunctor p₁ ≌ BasedCategory.ofFunctor p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) :
    (Indexed.explicit.functor (ofEquivalence e) χ₁ χ₂).FiberwiseEquivalence := sorry

/-- A bicategorical equivalence of fibred based categories induces a fiberwise equivalence on
the pseudofunctors defined by their selected cleavages. -/
instance Indexed.chosen.functor.fiberwiseEquivalence.ofEquivalence
    (e : BasedCategory.ofFunctor p₁ ≌ BasedCategory.ofFunctor p₂)
    [p₁.IsFibered] [p₂.IsFibered] :
    (Indexed.chosen.functor (ofEquivalence e)).FiberwiseEquivalence := sorry

end FixedOwnerEquivalence

end CartesianBasedFunctor

end CategoryTheory
