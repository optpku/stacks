module

public import ReasLib.AlgebraicTopology.Cech.Existence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coprojections into Cech conerves

The existence predicate for a fixed Cech conerve stores one wide-pushout instance in every
degree. This leaf exposes the corresponding head and vertex coprojections together with the
degreewise universal property, without requiring downstream statements to reconstruct those
instances from the dependent family.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]

namespace cechConerve

variable (f : Arrow C) [h : f.HasCechConerve]

/-- The coprojection from the factor indexed by a simplex vertex into a degree of the Cech
conerve. -/
@[stacks 016N "Cech-conerve vertex coprojection", stacks 019Z "Cech-conerve vertex coprojection"]
noncomputable def ι (n : SimplexCategory) (i : Fin (n.len + 1)) :
    f.right ⟶ f.cechConerve.obj n :=
  @WidePushout.ι (Fin (n.len + 1)) C _ f.left
    (fun _ ↦ f.right) (fun _ ↦ f.hom) (h n.len) i

/-- The coprojection from the source of the underlying arrow into a degree of the Cech
conerve. -/
@[stacks 016N "Cech-conerve head coprojection", stacks 019Z "Cech-conerve head coprojection"]
noncomputable def head (n : SimplexCategory) :
    f.left ⟶ f.cechConerve.obj n :=
  @WidePushout.head (Fin (n.len + 1)) C _ f.left
    (fun _ ↦ f.right) (fun _ ↦ f.hom) (h n.len)

/-- The underlying arrow followed by any vertex coprojection agrees with the head
coprojection. -/
@[reassoc (attr := simp), stacks 016N "Cech-conerve coprojection compatibility", stacks 019Z "Cech-conerve coprojection compatibility"]
theorem arrow_ι (n : SimplexCategory) (i : Fin (n.len + 1)) :
    f.hom ≫ ι f n i = head f n := sorry

/-- A simplex operator reindexes the vertex coprojections of the Cech conerve by its
underlying monotone map. -/
@[reassoc (attr := simp), stacks 016N "Cech-conerve vertex coprojection under reindexing", stacks 019Z "Cech-conerve vertex coprojection under reindexing"]
theorem ι_map {n m : SimplexCategory} (α : n ⟶ m) (i : Fin (n.len + 1)) :
    ι f n i ≫ f.cechConerve.map α = ι f m (α.toOrderHom i) := sorry

/-- Every simplex operator preserves the head coprojection of the Cech conerve. -/
@[reassoc (attr := simp), stacks 016N "Cech-conerve head coprojection under reindexing", stacks 019Z "Cech-conerve head coprojection under reindexing"]
theorem head_map {n m : SimplexCategory} (α : n ⟶ m) :
    head f n ≫ f.cechConerve.map α = head f m := sorry

/-- Construct a morphism from one degree of a Cech conerve from a head map and a compatible
family of vertex maps. -/
@[stacks 016N "Cech-conerve degreewise descent", stacks 019Z "Cech-conerve degreewise descent"]
noncomputable def desc {Z : C} (n : SimplexCategory)
    (b : f.left ⟶ Z) (p : Fin (n.len + 1) → (f.right ⟶ Z))
    (w : ∀ i, f.hom ≫ p i = b) :
    f.cechConerve.obj n ⟶ Z :=
  @WidePushout.desc (Fin (n.len + 1)) C _ f.left
    (fun _ ↦ f.right) (fun _ ↦ f.hom) (h n.len) Z b p w

/-- A Cech-conerve descent has the prescribed value on each vertex coprojection. -/
@[reassoc (attr := simp), stacks 016N "Cech-conerve descent vertex computation", stacks 019Z "Cech-conerve descent vertex computation"]
theorem ι_desc {Z : C} (n : SimplexCategory)
    (b : f.left ⟶ Z) (p : Fin (n.len + 1) → (f.right ⟶ Z))
    (w : ∀ i, f.hom ≫ p i = b) (i : Fin (n.len + 1)) :
    ι f n i ≫ desc f n b p w = p i := sorry

/-- A Cech-conerve descent has the prescribed value on the head coprojection. -/
@[reassoc (attr := simp), stacks 016N "Cech-conerve descent head computation", stacks 019Z "Cech-conerve descent head computation"]
theorem head_desc {Z : C} (n : SimplexCategory)
    (b : f.left ⟶ Z) (p : Fin (n.len + 1) → (f.right ⟶ Z))
    (w : ∀ i, f.hom ≫ p i = b) :
    head f n ≫ desc f n b p w = b := sorry

/-- Morphisms from a degree of a Cech conerve are determined by their values on the vertex
coprojections. -/
@[ext 1100, stacks 016N "Cech-conerve degreewise extensionality", stacks 019Z "Cech-conerve degreewise extensionality"]
theorem hom_ext {Z : C} (n : SimplexCategory)
    (g₁ g₂ : f.cechConerve.obj n ⟶ Z)
    (hι : ∀ i, ι f n i ≫ g₁ = ι f n i ≫ g₂) :
    g₁ = g₂ := sorry

end cechConerve

namespace mapCechConerve

variable {f g : Arrow C} [f.HasCechConerve] [g.HasCechConerve]

/-- A morphism of arrows acts on every Cech-conerve vertex coprojection through its right-hand
component. -/
@[reassoc (attr := simp), stacks 016N "Cech-conerve map on vertex coprojections", stacks 019Z "Cech-conerve map on vertex coprojections"]
theorem app_ι (F : f ⟶ g) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    cechConerve.ι f n i ≫ (Arrow.mapCechConerve F).app n =
      F.right ≫ cechConerve.ι g n i := sorry

/-- A morphism of arrows acts on every Cech-conerve head coprojection through its left-hand
component. -/
@[reassoc (attr := simp), stacks 016N "Cech-conerve map on head coprojections", stacks 019Z "Cech-conerve map on head coprojections"]
theorem app_head (F : f ⟶ g) (n : SimplexCategory) :
    cechConerve.head f n ≫ (Arrow.mapCechConerve F).app n =
      F.left ≫ cechConerve.head g n := sorry

end mapCechConerve

end CategoryTheory.Arrow
