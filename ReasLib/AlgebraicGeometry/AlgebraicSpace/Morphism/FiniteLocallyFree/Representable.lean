module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree

/-!
# Representable finite locally free morphisms of algebraic spaces

Finite local freeness tested on represented scheme pullbacks is equivalent to
affineness and finite local freeness of the pushforward structure module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A representable morphism of algebraic spaces over a scheme has finite locally
free pullbacks to all schemes if and only if it is affine and the direct image
of its structure sheaf is a finite locally free module on the target. -/
theorem finiteLocallyFree_presheaf_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.IsFiniteLocallyFree :
      MorphismProperty Scheme.{u})).presheaf f ↔
      Affine f ∧ SheafOfModules.IsFiniteLocallyFree
        (Modules.pushforwardStructureModule f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
