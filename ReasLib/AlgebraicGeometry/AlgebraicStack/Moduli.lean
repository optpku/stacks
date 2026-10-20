/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice

/-!
# Categorical moduli spaces of algebraic stacks

A morphism from an algebraic stack to an algebraic space is a categorical
moduli space when every morphism to an algebraic space factors uniquely
through it. Uniform and in-`C` variants quantify this over flat base change
and over a full subcategory of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` from an algebraic stack to an algebraic space is a
categorical moduli space if every morphism from `X` to an algebraic space
factors uniquely through `f`. -/
@[mk_iff]
class IsCategoricalModuliSpace {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) : Prop where
  /-- Every morphism `g : X ⟶ W.toGroupoids` to an algebraic space factors
  uniquely as a 2-commutative triangle through `f`. -/
  unique_factor {W : AlgebraicSpace S} (g : X ⟶ W.toGroupoids) :
    ∃! χ : Y ⟶ W, Nonempty (f ≫ AlgebraicSpace.toGroupoids.map χ ≅ g)

/-- A categorical moduli space has unique factorization of morphisms to
algebraic spaces through `f`. -/
theorem IsCategoricalModuliSpace.spec {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
    [IsCategoricalModuliSpace f] {W : AlgebraicSpace S}
    (g : X ⟶ W.toGroupoids) :
    ∃! χ : Y ⟶ W, Nonempty (f ≫ AlgebraicSpace.toGroupoids.map χ ≅ g) :=
  sorry

/-- The identity of an algebraic space is a categorical moduli space for that
space. -/
instance instIsCategoricalModuliSpace_id {S : Scheme.{u}} {Y : AlgebraicSpace S} :
    IsCategoricalModuliSpace (𝟙 Y.toGroupoids) :=
  sorry

/-- A morphism `f : X ⟶ Y` from an algebraic stack to an algebraic space is a
uniform categorical moduli space if every base change along a flat morphism of
algebraic spaces remains a categorical moduli space. -/
@[mk_iff]
class IsUniformCategoricalModuliSpace {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) : Prop where
  /-- Flat base change of `f` is a categorical moduli space. -/
  of_flat {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) [AlgebraicSpace.Flat h] :
    IsCategoricalModuliSpace (pullbackSnd f h)

/-- A uniform categorical moduli space remains a categorical moduli space after
every flat base change. -/
theorem IsUniformCategoricalModuliSpace.spec {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    (f : X ⟶ Y.toGroupoids) [IsUniformCategoricalModuliSpace f]
    {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) [AlgebraicSpace.Flat h] :
    IsCategoricalModuliSpace (pullbackSnd f h) :=
  sorry

/-- The identity of an algebraic space is a uniform categorical moduli space. -/
instance instIsUniformCategoricalModuliSpace_id {S : Scheme.{u}}
    {Y : AlgebraicSpace S} : IsUniformCategoricalModuliSpace (𝟙 Y.toGroupoids) :=
  sorry

/-- A uniform categorical moduli space is a categorical moduli space, by
identity base change. -/
instance instIsCategoricalModuliSpace_of_isUniform {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    (f : X ⟶ Y.toGroupoids) [IsUniformCategoricalModuliSpace f] :
    IsCategoricalModuliSpace f :=
  sorry

/-- A morphism `f : X ⟶ Y` from an algebraic stack to an algebraic space is a
categorical moduli space in a full subcategory `C` of algebraic spaces if `Y`
lies in `C` and every morphism from `X` to an object of `C` factors uniquely
through `f`. -/
@[mk_iff]
class IsCategoricalModuliSpaceIn {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S}
    (C : ObjectProperty (AlgebraicSpace S)) (f : X ⟶ Y.toGroupoids) : Prop where
  /-- The target algebraic space lies in `C`. -/
  obj_Y : C Y
  /-- Every morphism `g : X ⟶ W.toGroupoids` with `W` in `C` factors uniquely
  as a 2-commutative triangle through `f`. -/
  unique_factor {W : AlgebraicSpace S} (hW : C W) (g : X ⟶ W.toGroupoids) :
    ∃! χ : Y ⟶ W, Nonempty (f ≫ AlgebraicSpace.toGroupoids.map χ ≅ g)

/-- Being a categorical moduli space in `C` is membership of the target in `C`
together with unique factorization of morphisms to objects of `C`. -/
theorem isCategoricalModuliSpaceIn_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S}
    (C : ObjectProperty (AlgebraicSpace S)) (f : X ⟶ Y.toGroupoids) :
    IsCategoricalModuliSpaceIn C f ↔
      C Y ∧ ∀ {W : AlgebraicSpace S} (hW : C W) (g : X ⟶ W.toGroupoids),
        ∃! χ : Y ⟶ W, Nonempty (f ≫ AlgebraicSpace.toGroupoids.map χ ≅ g) :=
  sorry

/-- The identity of an algebraic space lying in `C` is a categorical moduli
space in `C`. -/
instance instIsCategoricalModuliSpaceIn_id {S : Scheme.{u}}
    {Y : AlgebraicSpace S} (C : ObjectProperty (AlgebraicSpace S)) [C.Is Y] :
    IsCategoricalModuliSpaceIn C (𝟙 Y.toGroupoids) :=
  sorry

/-- An ambient categorical moduli space whose target lies in `C` is a
categorical moduli space in `C`. -/
instance instIsCategoricalModuliSpaceIn_of_isCategoricalModuliSpace
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} {C : ObjectProperty (AlgebraicSpace S)}
    {f : X ⟶ Y.toGroupoids} [IsCategoricalModuliSpace f] [C.Is Y] :
    IsCategoricalModuliSpaceIn C f :=
  sorry

/-- A categorical moduli space in the full subcategory of all algebraic spaces
is a categorical moduli space. -/
instance instIsCategoricalModuliSpace_of_top {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    {f : X ⟶ Y.toGroupoids}
    [IsCategoricalModuliSpaceIn (⊤ : ObjectProperty (AlgebraicSpace S)) f] :
    IsCategoricalModuliSpace f :=
  sorry

/-- A categorical moduli space is a categorical moduli space in the full
subcategory of all algebraic spaces. -/
theorem isCategoricalModuliSpace_iff_in_top {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    (f : X ⟶ Y.toGroupoids) :
    IsCategoricalModuliSpace f ↔
      IsCategoricalModuliSpaceIn (⊤ : ObjectProperty (AlgebraicSpace S)) f :=
  sorry

/-- A morphism `f : X ⟶ Y` from an algebraic stack to an algebraic space is a
uniform categorical moduli space in a full subcategory `C` of algebraic spaces
if `Y` lies in `C` and every base change along a flat morphism in `C` is a
categorical moduli space in `C`. -/
@[mk_iff]
class IsUniformCategoricalModuliSpaceIn {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S}
    (C : ObjectProperty (AlgebraicSpace S)) (f : X ⟶ Y.toGroupoids) : Prop where
  /-- The target algebraic space lies in `C`. -/
  obj_Y : C Y
  /-- Flat base change of `f` along a morphism in `C` is a categorical moduli
  space in `C`. -/
  of_flat {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) (hY' : C Y')
      [AlgebraicSpace.Flat h] : IsCategoricalModuliSpaceIn C (pullbackSnd f h)

/-- Being a uniform categorical moduli space in `C` is membership of the target
in `C` together with stability of the in-`C` property under flat base change in
`C`. -/
theorem isUniformCategoricalModuliSpaceIn_spec {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    (C : ObjectProperty (AlgebraicSpace S)) (f : X ⟶ Y.toGroupoids) :
    IsUniformCategoricalModuliSpaceIn C f ↔
      C Y ∧ ∀ {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) (hY' : C Y'),
        AlgebraicSpace.Flat h →
          IsCategoricalModuliSpaceIn C (pullbackSnd f h) :=
  sorry

/-- The identity of an algebraic space lying in `C` is a uniform categorical
moduli space in `C`. -/
instance instIsUniformCategoricalModuliSpaceIn_id {S : Scheme.{u}}
    {Y : AlgebraicSpace S} (C : ObjectProperty (AlgebraicSpace S)) [C.Is Y] :
    IsUniformCategoricalModuliSpaceIn C (𝟙 Y.toGroupoids) :=
  sorry

/-- A uniform categorical moduli space in `C` is a categorical moduli space in
`C`, by identity base change. -/
instance instIsCategoricalModuliSpaceIn_of_isUniform {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    {C : ObjectProperty (AlgebraicSpace S)} {f : X ⟶ Y.toGroupoids}
    [IsUniformCategoricalModuliSpaceIn C f] : IsCategoricalModuliSpaceIn C f :=
  sorry

/-- An ambient uniform categorical moduli space whose target lies in `C` is a
uniform categorical moduli space in `C`. -/
instance instIsUniformCategoricalModuliSpaceIn_of_isUniform {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    {C : ObjectProperty (AlgebraicSpace S)} {f : X ⟶ Y.toGroupoids}
    [IsUniformCategoricalModuliSpace f] [C.Is Y] :
    IsUniformCategoricalModuliSpaceIn C f :=
  sorry

/-- A uniform categorical moduli space in the full subcategory of all algebraic
spaces is a uniform categorical moduli space. -/
instance instIsUniformCategoricalModuliSpace_of_top {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    {f : X ⟶ Y.toGroupoids}
    [IsUniformCategoricalModuliSpaceIn (⊤ : ObjectProperty (AlgebraicSpace S)) f] :
    IsUniformCategoricalModuliSpace f :=
  sorry

/-- A uniform categorical moduli space is a uniform categorical moduli space in
the full subcategory of all algebraic spaces. -/
theorem isUniformCategoricalModuliSpace_iff_in_top {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    (f : X ⟶ Y.toGroupoids) :
    IsUniformCategoricalModuliSpace f ↔
      IsUniformCategoricalModuliSpaceIn
        (⊤ : ObjectProperty (AlgebraicSpace S)) f :=
  sorry

/-- A morphism from an algebraic stack to an algebraic space is a uniform
categorical moduli space if every base change along a flat morphism from an
affine scheme is a categorical moduli space. -/
@[stacks 0DUJ]
theorem IsUniformCategoricalModuliSpace.of_forall_affine
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
    (hf : ∀ (Y' : Over S) [IsAffine Y'.left]
      (g : AlgebraicSpace.ofOver Y' ⟶ Y) [AlgebraicSpace.Flat g],
      IsCategoricalModuliSpace (pullbackSnd f g)) :
    IsUniformCategoricalModuliSpace f :=
  sorry

/-- A morphism from an algebraic stack to an algebraic space is a uniform
categorical moduli space if and only if every base change along a flat morphism
from an affine scheme is a categorical moduli space. -/
theorem isUniformCategoricalModuliSpace_iff_forall_affine
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) :
    IsUniformCategoricalModuliSpace f ↔
      ∀ (Y' : Over S) [IsAffine Y'.left]
        (g : AlgebraicSpace.ofOver Y' ⟶ Y) [AlgebraicSpace.Flat g],
        IsCategoricalModuliSpace (pullbackSnd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
