module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.FiberwiseEquivalence
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom-presheaf maps of universe-polymorphic cartesian functors

A cartesian based functor between fibred projections acts on their canonical Hom-presheaves.
When the two total categories have different morphism universes, the two presheaves are compared
after the minimal common `ULift` of their values.

The `Explicit` namespace is the choice-free owner: it takes source and target cleavages as data.
The `Chosen` namespace specializes this construction to `Functor.Cleavage.ofIsFibered`.
-/

@[expose] public section

universe uC vC uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

namespace CartesianBasedFunctor.HomPresheaf.Explicit

section MapImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The component at a slice object of the common-universe Hom-presheaf map induced by a
cartesian based functor and explicit source and target cleavages.

On a lifted section, the map removes `ULift`, applies the fiber functor, conjugates by the two
cartesian reindexing comparisons, and lifts the result back to the common universe. -/
private noncomputable def mapApp
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U : C} (x y : p₁.Fiber U) (W : (Over U)ᵒᵖ) :
    (((χ₁.toPseudofunctor).presheafHom x y) ⋙
      (uliftFunctor.{max vS₁ vS₂, vS₁} :
        Type vS₁ ⥤ Type (max vS₁ vS₂))).obj W ⟶
    (((χ₂.toPseudofunctor).presheafHom
      ((F.fiberFunctor U).obj x) ((F.fiberFunctor U).obj y)) ⋙
      (uliftFunctor.{max vS₁ vS₂, vS₂} :
        Type vS₂ ⥤ Type (max vS₁ vS₂))).obj W :=
  ↾fun δ ↦ ULift.up (
    (CartesianBasedFunctor.Reindex.mapIso F χ₁ χ₂ W.unop.hom x).hom ≫
      (F.fiberFunctor W.unop.left).map δ.down ≫
        (CartesianBasedFunctor.Reindex.mapIso F χ₁ χ₂ W.unop.hom y).inv)

/-- The construction-level component functions are natural in the opposite slice variable. -/
private theorem mapAppNaturality
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U : C} (x y : p₁.Fiber U) :
    ∀ ⦃W₁ W₂ : (Over U)ᵒᵖ⦄ (α : W₁ ⟶ W₂),
      (((χ₁.toPseudofunctor).presheafHom x y) ⋙
          (uliftFunctor.{max vS₁ vS₂, vS₁} :
            Type vS₁ ⥤ Type (max vS₁ vS₂))).map α ≫
        mapApp F χ₁ χ₂ x y W₂ =
      mapApp F χ₁ χ₂ x y W₁ ≫
        (((χ₂.toPseudofunctor).presheafHom
          ((F.fiberFunctor U).obj x) ((F.fiberFunctor U).obj y)) ⋙
          (uliftFunctor.{max vS₁ vS₂, vS₂} :
            Type vS₂ ⥤ Type (max vS₁ vS₂))).map α := sorry

/-- A universe-polymorphic cartesian based functor induces a map between the two canonical
Hom-presheaves after lifting their values to the minimal common universe. -/
@[stacks 042V "explicit-cleavage heterogeneous Hom-presheaf map"]
noncomputable def map
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U : C} (x y : p₁.Fiber U) :
    ((χ₁.toPseudofunctor).presheafHom x y) ⋙
        (uliftFunctor.{max vS₁ vS₂, vS₁} :
          Type vS₁ ⥤ Type (max vS₁ vS₂)) ⟶
      ((χ₂.toPseudofunctor).presheafHom
        ((F.fiberFunctor U).obj x) ((F.fiberFunctor U).obj y)) ⋙
        (uliftFunctor.{max vS₁ vS₂, vS₂} :
          Type vS₂ ⥤ Type (max vS₁ vS₂)) where
  app W := mapApp F χ₁ χ₂ x y W
  naturality := mapAppNaturality F χ₁ χ₂ x y

end MapImplementation

namespace map

/-- A component of the explicit-cleavage Hom-presheaf map is the lifted conjugation function. -/
@[simp, stacks 042V "component of explicit-cleavage Hom-presheaf map"]
theorem app
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U : C} (x y : p₁.Fiber U) (W : (Over U)ᵒᵖ) :
    (map F χ₁ χ₂ x y).app W = ↾fun δ ↦ ULift.up (
      (CartesianBasedFunctor.Reindex.mapIso F χ₁ χ₂ W.unop.hom x).hom ≫
        (F.fiberFunctor W.unop.left).map δ.down ≫
          (CartesianBasedFunctor.Reindex.mapIso F χ₁ χ₂ W.unop.hom y).inv) := sorry

/-- Pointwise, the explicit-cleavage Hom-presheaf map is the lifted conjugation of the fiber
functor's action by the cartesian reindexing comparisons. -/
@[simp, stacks 042V "pointwise explicit-cleavage Hom-presheaf map"]
theorem app.apply
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U : C} (x y : p₁.Fiber U) (W : (Over U)ᵒᵖ)
    (δ : (((χ₁.toPseudofunctor).presheafHom x y) ⋙
      (uliftFunctor.{max vS₁ vS₂, vS₁} :
        Type vS₁ ⥤ Type (max vS₁ vS₂))).obj W) :
    (map F χ₁ χ₂ x y).app W δ = ULift.up (
      (CartesianBasedFunctor.Reindex.mapIso F χ₁ χ₂ W.unop.hom x).hom ≫
        (F.fiberFunctor W.unop.left).map δ.down ≫
          (CartesianBasedFunctor.Reindex.mapIso F χ₁ χ₂ W.unop.hom y).inv) := sorry

/-- Fiberwise full faithfulness is sufficient for every explicit-cleavage common-universe
Hom-presheaf map to be an isomorphism. -/
@[stacks 042V "fiberwise full faithfulness gives explicit Hom-presheaf isomorphisms"]
theorem isIso_of_fiberwiseFullyFaithful
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (hF : ∀ V : C, Nonempty (F.fiberFunctor V).FullyFaithful)
    {U : C} (x y : p₁.Fiber U) :
    IsIso (map F χ₁ χ₂ x y) := sorry

/-- A cartesian based functor is fully faithful exactly when all common-universe
Hom-presheaf maps formed using explicit source and target cleavages are isomorphisms. -/
@[stacks 04WQ "heterogeneous full faithfulness via explicit Hom-presheaf maps"]
theorem fullyFaithful_iff_isIso
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) :
    Nonempty F.toFunctor.FullyFaithful ↔
      ∀ {U : C} (x y : p₁.Fiber U), IsIso (map F χ₁ χ₂ x y) := sorry

/-- An equivalence over the base induces isomorphisms on all explicit-cleavage Hom-presheaves
after the minimal common universe lift. -/
@[stacks 02ZA "heterogeneous Hom-presheaf invariance"]
theorem isIso_of_isEquivalence
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (hF : F.toBasedFunctor.IsEquivalence)
    {U : C} (x y : p₁.Fiber U) :
    IsIso (map F χ₁ χ₂ x y) := sorry

end map

end CartesianBasedFunctor.HomPresheaf.Explicit

namespace CartesianBasedFunctor.HomPresheaf.Chosen

variable [p₁.IsFibered] [p₂.IsFibered]

/-- The common-universe Hom-presheaf map obtained from the cleavages selected by the fibredness
instances of the source and target projections. -/
@[stacks 042V "chosen-cleavage heterogeneous Hom-presheaf map"]
noncomputable def map
    (F : CartesianBasedFunctor p₁ p₂) {U : C} (x y : p₁.Fiber U) :=
  Explicit.map F (Functor.Cleavage.ofIsFibered p₁)
    (Functor.Cleavage.ofIsFibered p₂) x y

namespace map

/-- A component of the selected-cleavage common-universe Hom-presheaf map is the corresponding
explicit-cleavage component. -/
@[simp, stacks 042V "component of selected-cleavage Hom-presheaf map"]
theorem app
    (F : CartesianBasedFunctor p₁ p₂) {U : C}
    (x y : p₁.Fiber U) (W : (Over U)ᵒᵖ) :
    (map F x y).app W =
      (Explicit.map F (Functor.Cleavage.ofIsFibered p₁)
        (Functor.Cleavage.ofIsFibered p₂) x y).app W := sorry

/-- Pointwise formula for the selected-cleavage common-universe Hom-presheaf map. -/
@[simp, stacks 042V "pointwise selected-cleavage Hom-presheaf map"]
theorem app.apply
    (F : CartesianBasedFunctor p₁ p₂) {U : C}
    (x y : p₁.Fiber U) (W : (Over U)ᵒᵖ)
    (δ : (((Functor.fiberPseudofunctor p₁).presheafHom x y) ⋙
      (uliftFunctor.{max vS₁ vS₂, vS₁} :
        Type vS₁ ⥤ Type (max vS₁ vS₂))).obj W) :
    (map F x y).app W δ = ULift.up (
      (CartesianBasedFunctor.Reindex.mapIso F
        (Functor.Cleavage.ofIsFibered p₁) (Functor.Cleavage.ofIsFibered p₂)
        W.unop.hom x).hom ≫
      (F.fiberFunctor W.unop.left).map δ.down ≫
      (CartesianBasedFunctor.Reindex.mapIso F
        (Functor.Cleavage.ofIsFibered p₁) (Functor.Cleavage.ofIsFibered p₂)
        W.unop.hom y).inv) := sorry

/-- Fiberwise full faithfulness makes every selected-cleavage common-universe Hom-presheaf map
an isomorphism. -/
@[stacks 042V "fiberwise full faithfulness gives selected Hom-presheaf isomorphisms"]
theorem isIso_of_fiberwiseFullyFaithful
    (F : CartesianBasedFunctor p₁ p₂)
    (hF : ∀ V : C, Nonempty (F.fiberFunctor V).FullyFaithful)
    {U : C} (x y : p₁.Fiber U) :
    IsIso (map F x y) := sorry

/-- A cartesian based functor is fully faithful exactly when all canonical common-universe
Hom-presheaf maps formed using the selected cleavages are isomorphisms. -/
@[stacks 04WQ "heterogeneous full faithfulness via canonical Hom-presheaf maps"]
theorem fullyFaithful_iff_isIso (F : CartesianBasedFunctor p₁ p₂) :
    Nonempty F.toFunctor.FullyFaithful ↔
      ∀ {U : C} (x y : p₁.Fiber U), IsIso (map F x y) := sorry

/-- An equivalence over the base induces isomorphisms on all selected-cleavage Hom-presheaves
after the minimal common universe lift. -/
@[stacks 02ZA "selected Hom-presheaf invariance under equivalence"]
theorem isIso_of_isEquivalence
    (F : CartesianBasedFunctor p₁ p₂) (hF : F.toBasedFunctor.IsEquivalence)
    {U : C} (x y : p₁.Fiber U) :
    IsIso (map F x y) := sorry

/-- Canonical common-universe Hom-presheaf maps of an equivalence over the base are available
to typeclass search. -/
@[stacks 02ZA "instance for selected Hom-presheaf equivalences"]
instance isIso
    (F : CartesianBasedFunctor p₁ p₂) [F.toBasedFunctor.IsEquivalence]
    {U : C} (x y : p₁.Fiber U) :
    IsIso (map F x y) := sorry

end map

end CartesianBasedFunctor.HomPresheaf.Chosen

end CategoryTheory

/- Axiom audit: the private construction-level component owns the explicit function on lifted Hom
sections. Any `sorryAx` in `Explicit.map` or `Chosen.map` is confined to naturality and to
proof-valued cartesian/coherence fields inherited by the canonical reindexing comparisons. -/
