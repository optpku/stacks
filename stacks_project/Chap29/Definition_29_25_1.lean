/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/-!
# Definition 29.25.1

This chapter entry records the pointwise and global flatness predicates for scheme morphisms and
module sheaves. The textbook fixes a quasi-coherent module sheaf, while the reusable predicates
apply to arbitrary module sheaves because their definitions use only stalks.
-/

/- Definition 29.25.1 (1): a scheme morphism is flat at a source point when the induced map from
the local ring at its image to the local ring at the source point is flat. -/
@[stacks 01U3] #check
  (AlgebraicGeometry.Scheme.Hom.flatAt :
    {X S : Scheme.{u}} → (X ⟶ S) → X → Prop)

/- Definition 29.25.1 (2): for the textbook's quasi-coherent module sheaf `ℱ`, flatness over the
base at `x` means that `ℱ`'s stalk at `x` is flat over the local ring at `f(x)`; the predicate is
valid for any module sheaf. -/
@[stacks 01U3] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt :
    {X S : Scheme.{u}} → X.Modules → (X ⟶ S) → X → Prop)

/- Definition 29.25.1 (3): a scheme morphism is flat exactly when it is flat at every source
point. -/
@[stacks 01U3] #check
  (AlgebraicGeometry.Scheme.Hom.flat_iff_forall_flatAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Flat f ↔ ∀ x : X, AlgebraicGeometry.Scheme.Hom.flatAt f x)

/- Definition 29.25.1 (4): the textbook's quasi-coherent module sheaf `ℱ` is flat over the base
exactly when it is flat over the base at every source point; the predicate is valid for any module
sheaf. -/
@[stacks 01U3] #check
  (AlgebraicGeometry.Scheme.Modules.flatOver_iff_forall_flatOverAt :
    ∀ {X S : Scheme.{u}} (ℱ : X.Modules) (f : X ⟶ S),
      AlgebraicGeometry.Scheme.Modules.flatOver ℱ f ↔
        ∀ x : X, AlgebraicGeometry.Scheme.Modules.flatOverAt ℱ f x)
