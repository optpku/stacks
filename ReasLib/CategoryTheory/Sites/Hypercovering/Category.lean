module

public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
public import Mathlib.CategoryTheory.InducedCategory

/-!
# The category of hypercoverings

Hypercoverings of a fixed target form the full induced category whose morphisms are simplicial
morphisms between their underlying fixed-target families.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Hypercovering

open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable {J : GrothendieckTopology C} {X : C}

/-- Hypercoverings of a fixed target inherit the category structure of their underlying
simplicial objects. -/
instance instCategory : Category (Hypercovering.{w} J X) :=
  inferInstanceAs <| Category
    (InducedCategory
      (SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X))
      fun K : Hypercovering.{w} J X ↦ K.toSimplicialObject)

/-- The fully faithful forgetful functor from hypercoverings to their underlying simplicial
fixed-target families. -/
abbrev forget : Hypercovering.{w} J X ⥤
    SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} X) :=
  inducedFunctor fun K : Hypercovering.{w} J X ↦ K.toSimplicialObject

/-- Build a hypercovering morphism from a morphism of the underlying simplicial objects. -/
abbrev homMk {K L : Hypercovering.{w} J X}
    (f : K.toSimplicialObject ⟶ L.toSimplicialObject) : K ⟶ L :=
  InducedCategory.homMk f

/-- The underlying simplicial map of a hypercovering morphism. -/
abbrev Hom.toSimplicial {K L : Hypercovering.{w} J X} (f : K ⟶ L) :
    K.toSimplicialObject ⟶ L.toSimplicialObject :=
  (forget (J := J) (X := X)).map f

/-- Hypercovering morphisms are determined by their underlying simplicial maps. -/
@[ext] theorem hom_ext {K L : Hypercovering.{w} J X} {f g : K ⟶ L}
    (h : Hom.toSimplicial f = Hom.toSimplicial g) : f = g := sorry

/-- The simplicial map underlying a morphism built by `homMk` is the original map. -/
@[simp] theorem homMk_toSimplicial {K L : Hypercovering.{w} J X}
    (f : K.toSimplicialObject ⟶ L.toSimplicialObject) :
    Hom.toSimplicial (homMk f) = f := sorry

end CategoryTheory.Hypercovering
