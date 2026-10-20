module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Composition

/-!
# Projective schemes over a base

This file defines the category of projective schemes over a fixed base and its base-change
functor, and records projectivity of the structural morphism from a fibre product.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The full subcategory of schemes over `S` whose structural morphism is projective. -/
abbrev ProjectiveOver (S : Scheme.{u}) :=
  MorphismProperty.Over @Projective ⊤ S

namespace ProjectiveOver

/-- Base change of projective schemes along a morphism of base schemes. -/
noncomputable def baseChange {S S' : Scheme.{u}} (g : S' ⟶ S) :
    ProjectiveOver S ⥤ ProjectiveOver S' :=
  MorphismProperty.Over.pullback @Projective ⊤ g

/-- The structural morphism of a base-changed projective scheme is the second pullback
projection. -/
theorem baseChange_obj_hom {S S' : Scheme.{u}} (g : S' ⟶ S) (X : ProjectiveOver S) :
    ((baseChange g).obj X).hom = pullback.snd X.hom g := sorry

end ProjectiveOver

/-- The structural morphism from the fibre product of two projective schemes over the same base
is projective. -/
theorem Projective.fiberProduct {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hf : Projective f) (hg : Projective g) :
    Projective (pullback.snd f g ≫ g) := sorry

end AlgebraicGeometry
