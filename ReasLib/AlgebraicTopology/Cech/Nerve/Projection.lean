module

public import ReasLib.AlgebraicTopology.Cech.Existence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Projections from Čech nerves

The existence predicate for a fixed Čech nerve stores one wide-pullback instance in every
degree. This leaf exposes the corresponding base and vertex projections without requiring
downstream statements to reconstruct those instances from the dependent family.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]

namespace cechNerve

variable (f : Arrow C) [h : f.HasCechNerve]

/-- The projection from a degree of the Čech nerve to the factor indexed by a simplex vertex. -/
@[stacks 016E "Čech-nerve vertex projection", stacks 018I "Čech-nerve vertex projection", stacks 019P "Čech-nerve vertex projection"]
noncomputable def π (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    f.cechNerve.obj n ⟶ f.left :=
  @WidePullback.π (Fin (n.unop.len + 1)) C _ f.right
    (fun _ ↦ f.left) (fun _ ↦ f.hom) (h n.unop.len) i

/-- The projection from a degree of the Čech nerve to the target of the underlying arrow. -/
@[stacks 016E "Čech-nerve base projection", stacks 018I "Čech-nerve base projection"]
noncomputable def base (n : SimplexCategoryᵒᵖ) :
    f.cechNerve.obj n ⟶ f.right :=
  @WidePullback.base (Fin (n.unop.len + 1)) C _ f.right
    (fun _ ↦ f.left) (fun _ ↦ f.hom) (h n.unop.len)

/-- Every Čech-nerve vertex projection agrees with the base projection after composition with
the underlying arrow. -/
@[reassoc (attr := simp), stacks 016E "Čech-nerve projection compatibility", stacks 018I "Čech-nerve projection compatibility"]
theorem π_arrow (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    π f n i ≫ f.hom = base f n := sorry

/-- A simplex operator reindexes the vertex projections of the Čech nerve by its underlying
monotone map. -/
@[reassoc (attr := simp), stacks 016E "Čech-nerve vertex projection under reindexing", stacks 018I "Čech-nerve vertex projection under reindexing"]
theorem map_π {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (i : Fin (m.unop.len + 1)) :
    f.cechNerve.map α ≫ π f m i = π f n (α.unop.toOrderHom i) := sorry

/-- Every simplex operator preserves the base projection of the Čech nerve. -/
@[reassoc (attr := simp), stacks 016E "Čech-nerve base projection under reindexing", stacks 018I "Čech-nerve base projection under reindexing"]
theorem map_base {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    f.cechNerve.map α ≫ base f m = base f n := sorry

/-- Construct a morphism to one degree of a Čech nerve from a base map and a compatible family
of vertex maps. -/
@[stacks 016E "Čech-nerve degreewise lift", stacks 018I "Čech-nerve degreewise lift"]
noncomputable def lift {Z : C} (n : SimplexCategoryᵒᵖ)
    (b : Z ⟶ f.right) (p : Fin (n.unop.len + 1) → (Z ⟶ f.left))
    (w : ∀ i, p i ≫ f.hom = b) :
    Z ⟶ f.cechNerve.obj n :=
  @WidePullback.lift (Fin (n.unop.len + 1)) C _ f.right
    (fun _ ↦ f.left) (fun _ ↦ f.hom) (h n.unop.len) Z b p w

/-- A Čech-nerve lift has the prescribed vertex projections. -/
@[reassoc (attr := simp), stacks 016E "Čech-nerve lift vertex projection", stacks 018I "Čech-nerve lift vertex projection"]
theorem lift_π {Z : C} (n : SimplexCategoryᵒᵖ)
    (b : Z ⟶ f.right) (p : Fin (n.unop.len + 1) → (Z ⟶ f.left))
    (w : ∀ i, p i ≫ f.hom = b) (i : Fin (n.unop.len + 1)) :
    lift f n b p w ≫ π f n i = p i := sorry

/-- A Čech-nerve lift has the prescribed base projection. -/
@[reassoc (attr := simp), stacks 016E "Čech-nerve lift base projection", stacks 018I "Čech-nerve lift base projection"]
theorem lift_base {Z : C} (n : SimplexCategoryᵒᵖ)
    (b : Z ⟶ f.right) (p : Fin (n.unop.len + 1) → (Z ⟶ f.left))
    (w : ∀ i, p i ≫ f.hom = b) :
    lift f n b p w ≫ base f n = b := sorry

/-- Morphisms into a degree of a Čech nerve are determined by their vertex projections. -/
@[ext 1100, stacks 016E "Čech-nerve degreewise extensionality", stacks 018I "Čech-nerve degreewise extensionality"]
theorem hom_ext {Z : C} (n : SimplexCategoryᵒᵖ)
    (g₁ g₂ : Z ⟶ f.cechNerve.obj n)
    (hπ : ∀ i, g₁ ≫ π f n i = g₂ ≫ π f n i) :
    g₁ = g₂ := sorry

end cechNerve

namespace mapCechNerve

variable {f g : Arrow C} [f.HasCechNerve] [g.HasCechNerve]

/-- A morphism of arrows acts on every Čech-nerve vertex projection through its left-hand
component. -/
@[reassoc (attr := simp), stacks 016E "Čech-nerve map on vertex projections", stacks 018I "Čech-nerve map on vertex projections"]
theorem app_π (F : f ⟶ g) (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    (Arrow.mapCechNerve F).app n ≫ cechNerve.π g n i =
      cechNerve.π f n i ≫ F.left := sorry

/-- A morphism of arrows acts on every Čech-nerve base projection through its right-hand
component. -/
@[reassoc (attr := simp), stacks 016E "Čech-nerve map on base projections", stacks 018I "Čech-nerve map on base projections"]
theorem app_base (F : f ⟶ g) (n : SimplexCategoryᵒᵖ) :
    (Arrow.mapCechNerve F).app n ≫ cechNerve.base g n =
      cechNerve.base f n ≫ F.right := sorry

end mapCechNerve

end CategoryTheory.Arrow
