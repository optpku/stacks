/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Graph
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Symmetry.Equivalence
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

private theorem uniqueFactor_of_equivalence {S : Scheme.{u}}
    {X X' : GroupoidsOver S} {Y W : AlgebraicSpace S}
    (e : X ≌ X') (f : X ⟶ Y.toGroupoids) (f' : X' ⟶ Y.toGroupoids)
    (hf : Nonempty (e.hom ≫ f' ≅ f)) (g : X' ⟶ W.toGroupoids)
    (h : ∃! χ : Y ⟶ W, Nonempty (f ≫ AlgebraicSpace.toGroupoids.map χ ≅ e.hom ≫ g)) :
    ∃! χ : Y ⟶ W, Nonempty (f' ≫ AlgebraicSpace.toGroupoids.map χ ≅ g) := by
  rcases hf with ⟨i⟩
  have factor_iff (χ : Y ⟶ W) :
      Nonempty (f' ≫ AlgebraicSpace.toGroupoids.map χ ≅ g) ↔
        Nonempty (f ≫ AlgebraicSpace.toGroupoids.map χ ≅ e.hom ≫ g) := by
    constructor
    · rintro ⟨a⟩
      exact ⟨Bicategory.whiskerRightIso i.symm _ ≪≫ (α_ _ _ _) ≪≫
        Bicategory.whiskerLeftIso e.hom a⟩
    · rintro ⟨a⟩
      let b := (α_ e.hom f' (AlgebraicSpace.toGroupoids.map χ)).symm ≪≫
        Bicategory.whiskerRightIso i _ ≪≫ a
      exact ⟨(λ_ _).symm ≪≫ Bicategory.whiskerRightIso e.counit.symm _ ≪≫
        (α_ _ _ _) ≪≫ Bicategory.whiskerLeftIso e.inv b ≪≫
        (α_ _ _ _).symm ≪≫ Bicategory.whiskerRightIso e.counit _ ≪≫ (λ_ _)⟩
  rcases h with ⟨χ, hχ, huniq⟩
  exact ⟨χ, (factor_iff χ).mpr hχ, fun ψ hψ ↦ huniq ψ ((factor_iff ψ).mp hψ)⟩

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
  IsCategoricalModuliSpace.unique_factor g

/-- The identity of an algebraic space is a categorical moduli space for that
space. -/
instance instIsCategoricalModuliSpace_id {S : Scheme.{u}} {Y : AlgebraicSpace S} :
    IsCategoricalModuliSpace (𝟙 Y.toGroupoids) :=
  by
    refine ⟨fun g ↦ ?_⟩
    refine ⟨AlgebraicSpace.toGroupoids.eval g, ?_, ?_⟩
    · rcases (AlgebraicSpace.toGroupoids.eval.eq_iff_isomorphic _ _).mp
        (AlgebraicSpace.toGroupoids.eval.map (AlgebraicSpace.toGroupoids.eval g)) with ⟨e⟩
      exact ⟨(λ_ _) ≪≫ e⟩
    · rintro χ ⟨e⟩
      exact (AlgebraicSpace.toGroupoids.eval.map χ).symm.trans
        (AlgebraicSpace.toGroupoids.eval.eq_of_hom ((λ_ _).inv ≫ e.hom))

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
  IsUniformCategoricalModuliSpace.of_flat h

/-- The identity of an algebraic space is a uniform categorical moduli space. -/
instance instIsUniformCategoricalModuliSpace_id {S : Scheme.{u}}
    {Y : AlgebraicSpace S} : IsUniformCategoricalModuliSpace (𝟙 Y.toGroupoids) :=
  by
    refine ⟨fun {Y'} h ↦ ⟨fun g ↦ ?_⟩⟩
    let e : Y'.toGroupoids ≌ pullback (𝟙 Y.toGroupoids) h :=
      (TwoFibreProduct.graph.equivalence (AlgebraicSpace.toGroupoids.map h)).trans
        (TwoFibreProduct.swap.equivalence (AlgebraicSpace.toGroupoids.map h) (𝟙 _))
    have he : Nonempty (e.hom ≫ pullbackSnd (𝟙 Y.toGroupoids) h ≅ 𝟙 _) := by
      exact ⟨(α_ _ _ _) ≪≫
        Bicategory.whiskerLeftIso _
          (TwoFibreProduct.swap.sndIso (AlgebraicSpace.toGroupoids.map h) (𝟙 _)) ≪≫
        eqToIso (TwoFibreProduct.graph.fst (AlgebraicSpace.toGroupoids.map h))⟩
    exact uniqueFactor_of_equivalence e _ _ he g
      (IsCategoricalModuliSpace.spec (𝟙 Y'.toGroupoids) (e.hom ≫ g))

/-- A uniform categorical moduli space is a categorical moduli space, by
identity base change. -/
instance instIsCategoricalModuliSpace_of_isUniform {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    (f : X ⟶ Y.toGroupoids) [IsUniformCategoricalModuliSpace f] :
    IsCategoricalModuliSpace f :=
  by
    have h := IsUniformCategoricalModuliSpace.spec f (𝟙 Y)
    refine ⟨fun g ↦ uniqueFactor_of_equivalence
      (TwoFibreProduct.graph.equivalence f).symm (pullbackSnd f (𝟙 Y)) f
      ⟨TwoFibreProduct.comparisonIso f (𝟙 _) ≪≫ (ρ_ _)⟩ g ?_⟩
    exact h.unique_factor _

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
  by
    constructor
    · intro h
      exact ⟨h.obj_Y, h.unique_factor⟩
    · rintro ⟨hY, h⟩
      exact ⟨hY, h⟩

/-- The identity of an algebraic space lying in `C` is a categorical moduli
space in `C`. -/
instance instIsCategoricalModuliSpaceIn_id {S : Scheme.{u}}
    {Y : AlgebraicSpace S} (C : ObjectProperty (AlgebraicSpace S)) [C.Is Y] :
    IsCategoricalModuliSpaceIn C (𝟙 Y.toGroupoids) :=
  ⟨C.prop_of_is Y, fun _ g ↦ IsCategoricalModuliSpace.spec _ g⟩

/-- An ambient categorical moduli space whose target lies in `C` is a
categorical moduli space in `C`. -/
instance instIsCategoricalModuliSpaceIn_of_isCategoricalModuliSpace
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} {C : ObjectProperty (AlgebraicSpace S)}
    {f : X ⟶ Y.toGroupoids} [IsCategoricalModuliSpace f] [C.Is Y] :
    IsCategoricalModuliSpaceIn C f :=
  ⟨C.prop_of_is Y, fun _ g ↦ IsCategoricalModuliSpace.spec f g⟩

/-- A categorical moduli space in the full subcategory of all algebraic spaces
is a categorical moduli space. -/
instance instIsCategoricalModuliSpace_of_top {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    {f : X ⟶ Y.toGroupoids}
    [IsCategoricalModuliSpaceIn (⊤ : ObjectProperty (AlgebraicSpace S)) f] :
    IsCategoricalModuliSpace f :=
  ⟨fun g ↦ IsCategoricalModuliSpaceIn.unique_factor
    (C := ⊤) (f := f) (by trivial) g⟩

/-- A categorical moduli space is a categorical moduli space in the full
subcategory of all algebraic spaces. -/
theorem isCategoricalModuliSpace_iff_in_top {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    (f : X ⟶ Y.toGroupoids) :
    IsCategoricalModuliSpace f ↔
      IsCategoricalModuliSpaceIn (⊤ : ObjectProperty (AlgebraicSpace S)) f :=
  by
    constructor
    · intro h
      exact ⟨by trivial, fun _ g ↦ h.unique_factor g⟩
    · intro h
      exact ⟨fun g ↦ h.unique_factor (by trivial) g⟩

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
  by
    constructor
    · intro h
      exact ⟨h.obj_Y, fun g hY' _ ↦ h.of_flat g hY'⟩
    · rintro ⟨hY, h⟩
      exact ⟨hY, fun g hY' ↦ h g hY' inferInstance⟩

/-- The identity of an algebraic space lying in `C` is a uniform categorical
moduli space in `C`. -/
instance instIsUniformCategoricalModuliSpaceIn_id {S : Scheme.{u}}
    {Y : AlgebraicSpace S} (C : ObjectProperty (AlgebraicSpace S)) [C.Is Y] :
    IsUniformCategoricalModuliSpaceIn C (𝟙 Y.toGroupoids) :=
  ⟨C.prop_of_is Y, fun h hY' ↦
    ⟨hY', fun _ g ↦
      (IsUniformCategoricalModuliSpace.spec (𝟙 Y.toGroupoids) h).unique_factor g⟩⟩

/-- A uniform categorical moduli space in `C` is a categorical moduli space in
`C`, by identity base change. -/
instance instIsCategoricalModuliSpaceIn_of_isUniform {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    {C : ObjectProperty (AlgebraicSpace S)} {f : X ⟶ Y.toGroupoids}
    [IsUniformCategoricalModuliSpaceIn C f] : IsCategoricalModuliSpaceIn C f :=
  by
    have h := IsUniformCategoricalModuliSpaceIn.of_flat (C := C) (f := f)
      (𝟙 Y) (IsUniformCategoricalModuliSpaceIn.obj_Y (C := C) (f := f))
    refine ⟨h.obj_Y, fun hW g ↦ uniqueFactor_of_equivalence
      (TwoFibreProduct.graph.equivalence f).symm (pullbackSnd f (𝟙 Y)) f
      ⟨TwoFibreProduct.comparisonIso f (𝟙 _) ≪≫ (ρ_ _)⟩ g ?_⟩
    exact h.unique_factor hW _

/-- An ambient uniform categorical moduli space whose target lies in `C` is a
uniform categorical moduli space in `C`. -/
instance instIsUniformCategoricalModuliSpaceIn_of_isUniform {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    {C : ObjectProperty (AlgebraicSpace S)} {f : X ⟶ Y.toGroupoids}
    [IsUniformCategoricalModuliSpace f] [C.Is Y] :
    IsUniformCategoricalModuliSpaceIn C f :=
  ⟨C.prop_of_is Y, fun h hY' ↦
    ⟨hY', fun _ g ↦ (IsUniformCategoricalModuliSpace.spec f h).unique_factor g⟩⟩

/-- A uniform categorical moduli space in the full subcategory of all algebraic
spaces is a uniform categorical moduli space. -/
instance instIsUniformCategoricalModuliSpace_of_top {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    {f : X ⟶ Y.toGroupoids}
    [IsUniformCategoricalModuliSpaceIn (⊤ : ObjectProperty (AlgebraicSpace S)) f] :
    IsUniformCategoricalModuliSpace f :=
  ⟨fun h ↦ ⟨fun g ↦
    (IsUniformCategoricalModuliSpaceIn.of_flat
      (C := ⊤) (f := f) h (by trivial)).unique_factor (by trivial) g⟩⟩

/-- A uniform categorical moduli space is a uniform categorical moduli space in
the full subcategory of all algebraic spaces. -/
theorem isUniformCategoricalModuliSpace_iff_in_top {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Y : AlgebraicSpace S}
    (f : X ⟶ Y.toGroupoids) :
    IsUniformCategoricalModuliSpace f ↔
      IsUniformCategoricalModuliSpaceIn
        (⊤ : ObjectProperty (AlgebraicSpace S)) f :=
  by
    constructor
    · intro h
      exact ⟨by trivial, fun g _ ↦
        ⟨by trivial, fun _ k ↦ (h.of_flat g).unique_factor k⟩⟩
    · intro h
      exact ⟨fun g ↦
        ⟨fun k ↦ (h.of_flat g (by trivial)).unique_factor (by trivial) k⟩⟩

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
  by
    constructor
    · intro h Y' _ g _
      exact h.of_flat g
    · intro h
      exact IsUniformCategoricalModuliSpace.of_forall_affine f h

end AlgebraicGeometry.AlgebraicStack
