module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.Composition

/-!
# Quasi-projective schemes over a base

This file defines the category of quasi-projective schemes over a fixed base and its
base-change functor, and records quasi-projectivity of a fibre-product structural morphism.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The full subcategory of schemes over `S` whose structural morphism is quasi-projective. -/
abbrev QuasiProjectiveOver (S : Scheme.{u}) :=
  MorphismProperty.Over @QuasiProjective ⊤ S

namespace QuasiProjectiveOver

/-- Base change of quasi-projective schemes along a morphism of base schemes. -/
noncomputable def baseChange {S S' : Scheme.{u}} (g : S' ⟶ S) :
    QuasiProjectiveOver S ⥤ QuasiProjectiveOver S' :=
  MorphismProperty.Over.pullback @QuasiProjective ⊤ g

/-- The structural morphism of a base-changed quasi-projective scheme is the second pullback
projection. -/
theorem baseChange_obj_hom {S S' : Scheme.{u}} (g : S' ⟶ S) (X : QuasiProjectiveOver S) :
    ((baseChange g).obj X).hom = pullback.snd X.hom g := sorry

end QuasiProjectiveOver

/-- The structural morphism from the fibre product of two quasi-projective schemes over a base
admitting an ample invertible module is quasi-projective. -/
theorem QuasiProjective.fiberProduct
    {X Y S : Scheme.{u}} (hS : Scheme.Modules.HasAmpleInvertibleModule S)
    (f : X ⟶ S) (g : Y ⟶ S) (hf : QuasiProjective f) (hg : QuasiProjective g) :
    QuasiProjective (pullback.snd f g ≫ g) := sorry

end AlgebraicGeometry
