/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_5_3_Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.BaseChange

/-!
# Base change for conormal sheaves of immersions of algebraic spaces

The canonical comparison `f^* C_{Z'/X'} ⟶ C_{Z/X}` associated to a cartesian
square of immersions of algebraic spaces is an epimorphism, and is an
isomorphism when the ambient morphism is flat.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal

variable {S : Scheme.{u}}
variable {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']

variable (sq : IsPullback f i i' g)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map_epi_of_isPullback sq :
    Epi (map sq.toCommSq))

variable [Flat g]

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map_isIso_of_isPullback_of_flat sq :
    IsIso (map sq.toCommSq))

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal
