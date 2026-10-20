/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# The algebraic space of finite open subspaces

The finite-part functor of a separated, locally finite-type morphism of algebraic
spaces is an algebraic space with an étale structure morphism to the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The finite-part functor of a separated morphism of algebraic spaces that is
locally of finite type is an algebraic space. -/
instance instIsAlgebraicSpace (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] :
    IsAlgebraicSpace (finitePart f) :=
  sorry

/-- The algebraic space associated to the finite-part functor `(X/Y)_fin`. -/
def space (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (finitePart f)

/-- The functor of points of `space f` is `finitePart f`. -/
theorem space_functorOfPoints (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] :
    (space f).functorOfPoints = finitePart f :=
  rfl

/-- The structure morphism `(X/Y)_fin ⟶ Y`, as a morphism of algebraic spaces. -/
def spaceHom (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] : space f ⟶ Y :=
  toY f

/-- The structure morphism `spaceHom f` is the natural transformation `toY f`. -/
theorem spaceHom_eq (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] :
    spaceHom f = toY f :=
  rfl

/-- The structure morphism of the finite part of a separated, locally finite-type
morphism of algebraic spaces is étale. -/
instance instEtale_spaceHom (f : X ⟶ Y) [Separated f] [LocallyOfFiniteType f] :
    Etale (spaceHom f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
