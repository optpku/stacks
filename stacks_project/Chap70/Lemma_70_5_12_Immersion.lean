/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

/-!
# Immersion and monomorphism descent along directed affine limits of algebraic spaces

If `Y ⟶ X` is a morphism of algebraic spaces over an algebraic space `B`, and `X`
is a specified directed inverse limit of algebraic spaces over `B` with affine
transition morphisms, then a closed immersion, immersion, isomorphism, or
monomorphism `Y ⟶ X` descends to `Y ⟶ X_i` for all sufficiently large stages,
under the clause-specific quasi-compactness, quasi-separatedness, finite-type,
finite-presentation, and closed-transition hypotheses.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- A closed immersion into the limit of a directed inverse system of quasi-compact
algebraic spaces over an algebraic space, with affine transition morphisms, is a
closed immersion into every sufficiently large stage, provided its source is
locally of finite type over the base. -/
theorem exists_eventually_isClosedImmersion_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj B)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ B) [AlgebraicSpace.IsClosedImmersion f]
    [AlgebraicSpace.LocallyOfFiniteType g] (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → AlgebraicSpace.IsClosedImmersion (f ≫ c.π.app i') :=
  sorry

/-- A closed immersion into the limit of a directed inverse system of quasi-compact
algebraic spaces over an algebraic space, with affine transition morphisms, is a
closed immersion into some stage, provided its source is locally of finite type
over the base. -/
theorem exists_isClosedImmersion_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj B)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ B) [AlgebraicSpace.IsClosedImmersion f]
    [AlgebraicSpace.LocallyOfFiniteType g] (hfg : f ≫ σlim = g) :
    ∃ i : I, AlgebraicSpace.IsClosedImmersion (f ≫ c.π.app i) := sorry

/-- An immersion into the limit of a directed inverse system of absolutely
quasi-separated algebraic spaces over an algebraic space, with affine transition
morphisms, is an immersion into every sufficiently large stage, provided its
source is quasi-compact and locally of finite type over the base. -/
theorem exists_eventually_isImmersion_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj B)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [IsQuasiCompact Y] (f : Y ⟶ c.pt) (g : Y ⟶ B)
    [AlgebraicSpace.IsImmersion f] [AlgebraicSpace.LocallyOfFiniteType g]
    (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → AlgebraicSpace.IsImmersion (f ≫ c.π.app i') :=
  sorry

/-- An immersion into the limit of a directed inverse system of absolutely
quasi-separated algebraic spaces over an algebraic space, with affine transition
morphisms, is an immersion into some stage, provided its source is quasi-compact
and locally of finite type over the base. -/
theorem exists_isImmersion_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj B)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [IsQuasiCompact Y] (f : Y ⟶ c.pt) (g : Y ⟶ B)
    [AlgebraicSpace.IsImmersion f] [AlgebraicSpace.LocallyOfFiniteType g]
    (hfg : f ≫ σlim = g) :
    ∃ i : I, AlgebraicSpace.IsImmersion (f ≫ c.π.app i) := sorry

/-- An isomorphism to the limit of a directed inverse system of quasi-compact
algebraic spaces over an algebraic space, with affine closed-immersion transition
morphisms and locally finite-type stage morphisms, is an isomorphism to every
sufficiently large stage when the source is locally of finite presentation over
the base. -/
theorem exists_eventually_isIso_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj B)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, AlgebraicSpace.LocallyOfFiniteType (t.app i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [∀ {i i' : I} (hii' : i ≤ i'), AlgebraicSpace.IsClosedImmersion (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ B) [IsIso f]
    [AlgebraicSpace.LocallyOfFinitePresentation g] (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsIso (f ≫ c.π.app i') := sorry

/-- An isomorphism to the limit of a directed inverse system of quasi-compact
algebraic spaces over an algebraic space, with affine closed-immersion transition
morphisms and locally finite-type stage morphisms, is an isomorphism to some
stage when the source is locally of finite presentation over the base. -/
theorem exists_isIso_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj B)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, AlgebraicSpace.LocallyOfFiniteType (t.app i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [∀ {i i' : I} (hii' : i ≤ i'), AlgebraicSpace.IsClosedImmersion (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ B) [IsIso f]
    [AlgebraicSpace.LocallyOfFinitePresentation g] (hfg : f ≫ σlim = g) :
    ∃ i : I, IsIso (f ≫ c.π.app i) := sorry

/-- A monomorphism into the limit of a directed inverse system of absolutely
quasi-separated algebraic spaces over an algebraic space, with affine transition
morphisms, is a monomorphism into every sufficiently large stage, provided its
source is quasi-compact and locally of finite type over the base. -/
theorem exists_eventually_mono_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj B)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [IsQuasiCompact Y] (f : Y ⟶ c.pt) (g : Y ⟶ B) [Mono f]
    [AlgebraicSpace.LocallyOfFiniteType g] (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → Mono (f ≫ c.π.app i') := sorry

/-- A monomorphism into the limit of a directed inverse system of absolutely
quasi-separated algebraic spaces over an algebraic space, with affine transition
morphisms, is a monomorphism into some stage, provided its source is
quasi-compact and locally of finite type over the base. -/
theorem exists_mono_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj B)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [IsQuasiCompact Y] (f : Y ⟶ c.pt) (g : Y ⟶ B) [Mono f]
    [AlgebraicSpace.LocallyOfFiniteType g] (hfg : f ≫ σlim = g) :
    ∃ i : I, Mono (f ≫ c.π.app i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
