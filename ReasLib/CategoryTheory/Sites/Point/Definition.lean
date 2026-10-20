module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Functor.PresheafFiber
public import ReasLib.CategoryTheory.Sites.Point.Construction

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- The stalk functor obtained by restricting the presheaf fiber of `u` to sheaves. -/
noncomputable def siteStalk (J : GrothendieckTopology C) (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] : Sheaf J (Type w) ⥤ Type w :=
  sheafToPresheaf J (Type w) ⋙ u.presheafFiber

/-- The canonical stalk functor preserves finite limits. -/
def stalkPreservesFiniteLimits (J : GrothendieckTopology C) (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] : Prop :=
  PreservesFiniteLimits (siteStalk J u)

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Precoverage

variable {C : Type u} [Category.{v} C]

/-- Every element of a functor's value lifts along an arrow of each covering presieve. -/
def coverSurjective (K : Precoverage C) (F : C ⥤ Type w) : Prop :=
  ∀ {U : C} (R : Presieve U), R ∈ K U → ∀ element : F.obj U,
    ∃ (X : C) (arrow : X ⟶ U) (_ : R arrow) (lift : F.obj X), F.map arrow lift = element

/-- Pullback comparisons for covering arrows against arbitrary arrows are bijective
whenever the corresponding pullback exists. -/
def coverPullbackBijective (K : Precoverage C) (F : C ⥤ Type w) : Prop :=
  ∀ {X U V : C} (R : Presieve U), R ∈ K U → ∀ (coverArrow : X ⟶ U), R coverArrow →
    ∀ (arrow : V ⟶ U) [HasPullback coverArrow arrow],
      Function.Bijective (pullbackComparison F coverArrow arrow)

/-- A site point is a set-valued functor satisfying covering surjectivity, covering
pullback bijectivity, and left exactness of its canonical stalk on sheaves. -/
def IsSitePoint (K : Precoverage C) [K.HasIsos] [K.IsStableUnderComposition]
    [K.IsStableUnderBaseChange] [K.HasPullbacks] (F : C ⥤ Type (max u v)) : Prop :=
  coverSurjective K F ∧ coverPullbackBijective K F ∧
    GrothendieckTopology.stalkPreservesFiniteLimits K.toGrothendieck F

/-- Surjectivity on covering presieves is equivalent to element lifting on covering
sieves of the generated Grothendieck topology. -/
theorem coverSurjective_iff_coversLift (K : Precoverage C) [K.HasIsos]
    [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (F : C ⥤ Type w) :
    coverSurjective K F ↔ GrothendieckTopology.Point.Fiber.coversLift K.toGrothendieck F := sorry

end CategoryTheory.Precoverage
