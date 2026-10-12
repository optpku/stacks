/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
# Diagonal coproduct functors

For a fixed indexing type `J`, this file packages the coproduct of a constant `J`-indexed
family as an endofunctor.  It assumes only the constant coproducts used by the construction,
rather than coproducts of every `J`-indexed family.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Limits.Sigma

variable {C : Type u} [Category.{v} C]
variable (J : Type w) [∀ X : C, HasCoproduct (fun _ : J ↦ X)]

/-- The componentwise map on a constant coproduct preserves identity morphisms. -/
@[stacks 0192 "identity map on a constant coefficient coproduct"]
theorem diagonal.map_id (X : C) :
    Sigma.map (fun _ : J ↦ 𝟙 X) =
      𝟙 (∐ fun _ : J ↦ X) := sorry

/-- The componentwise map on a constant coproduct preserves composition. -/
@[stacks 0192 "composition of maps on constant coefficient coproducts"]
theorem diagonal.map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Sigma.map (fun _ : J ↦ f ≫ g) =
      Sigma.map (fun _ : J ↦ f) ≫
        Sigma.map (fun _ : J ↦ g) := sorry

/-- The endofunctor taking an object to the coproduct of a constant `J`-indexed family. -/
@[stacks 0192 "constant coefficient coproduct functor"]
noncomputable def diagonal : C ⥤ C where
  obj X := ∐ fun _ : J ↦ X
  map f := Sigma.map fun _ ↦ f
  map_id X := diagonal.map_id J X
  map_comp f g := diagonal.map_comp J f g

/-- The diagonal coproduct functor has the expected object value. -/
@[simp, stacks 0192 "constant coefficient coproduct object formula"]
theorem diagonal_obj (X : C) :
    (diagonal J).obj X = ∐ fun _ : J ↦ X := sorry

/-- The diagonal coproduct functor acts componentwise on morphisms. -/
@[simp, stacks 0192 "constant coefficient coproduct map formula"]
theorem diagonal_map {X Y : C} (f : X ⟶ Y) :
    (diagonal J).map f = Sigma.map (fun _ : J ↦ f) := sorry

/-- A morphism commutes with every inclusion into a constant coproduct. -/
@[stacks 0192 "naturality of a constant coefficient coproduct inclusion"]
theorem diagonal.ι_naturality {K : Type w}
    [∀ X : C, HasCoproduct (fun _ : K ↦ X)]
    (i : K) {X Y : C} (f : X ⟶ Y) :
    f ≫ Sigma.ι (fun _ : K ↦ Y) i =
      Sigma.ι (fun _ : K ↦ X) i ≫ (diagonal K).map f := sorry

/-- Inclusion of one fixed summand, natural in the repeated object. -/
@[stacks 0192 "natural inclusion into a constant coefficient coproduct"]
noncomputable def diagonal.ι {K : Type w}
    [∀ X : C, HasCoproduct (fun _ : K ↦ X)] (i : K) :
    𝟭 C ⟶ diagonal K where
  app X := Sigma.ι (fun _ : K ↦ X) i
  naturality _ _ f := diagonal.ι_naturality i f

/-- A component of the natural inclusion is the corresponding coproduct inclusion. -/
@[simp, stacks 0192 "component of a constant coefficient coproduct inclusion"]
theorem diagonal.ι_app {K : Type w}
    [∀ X : C, HasCoproduct (fun _ : K ↦ X)] (i : K) (X : C) :
    (diagonal.ι i).app X =
      Sigma.ι (fun _ : K ↦ X) i := sorry

end CategoryTheory.Limits.Sigma
