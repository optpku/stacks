/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Flatness loci and arbitrary base change

For composable morphisms of algebraic spaces, the flatness locus over the
intermediate space is open and commutes with arbitrary base change when the
source is locally of finite presentation and flat over the final base and the
intermediate space is locally of finite type over it.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For composable morphisms of algebraic spaces, the flatness locus over the
intermediate space is open when the source is locally of finite presentation
and flat over the final base and the intermediate space is locally of finite
type over it. -/
@[stacks 05X3]
theorem isOpen_flatAt {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
    [Flat (f ≫ h)] [LocallyOfFiniteType h] :
    IsOpen {x | FlatAt f x} :=
  sorry

/-- For composable morphisms of algebraic spaces, the flatness locus over the
intermediate space commutes with arbitrary base change when the source is
locally of finite presentation and flat over the final base and the intermediate
space is locally of finite type over it. -/
@[stacks 05X3]
theorem flatAt_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [Flat (f ≫ h)]
    [LocallyOfFiniteType h] :
    {x' | FlatAt (overBaseChange f h g) x'} =
      Points.map (pullback.fst (f ≫ h) g) ⁻¹' {x | FlatAt f x} :=
  sorry

/-- A point of `Points (pullback (f ≫ h) g)` lies in the pointwise flatness
locus of `overBaseChange f h g` if and only if its image under
`Points.map (pullback.fst (f ≫ h) g)` lies in `{x | FlatAt f x}`. -/
theorem mem_flatAt_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [Flat (f ≫ h)]
    [LocallyOfFiniteType h] (x' : Points (pullback (f ≫ h) g)) :
    FlatAt (overBaseChange f h g) x' ↔
      Points.map (pullback.fst (f ≫ h) g) x' ∈ {x | FlatAt f x} := by
  change x' ∈ {x' | FlatAt (overBaseChange f h g) x'} ↔ _
  rw [flatAt_baseChange_eq_preimage f h g]
  rfl

end AlgebraicGeometry.AlgebraicSpace
