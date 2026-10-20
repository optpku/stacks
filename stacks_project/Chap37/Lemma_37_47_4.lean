/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Topology
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped Topology

universe u

/- Lemma 37.47.4 (1): if a point is the unique point of its fiber under a finite morphism,
every neighborhood of that point contains the inverse image of a neighborhood of its image. -/
@[stacks 05B8]
#check (AlgebraicGeometry.IsFinite.exists_nhds_preimage_subset_of_fiber_eq_singleton :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (h_fiber : f ⁻¹' {f x} = {x}) (U : Set X) (hU : U ∈ 𝓝 x),
    ∃ V : Set Y, V ∈ 𝓝 (f x) ∧ f ⁻¹' V ⊆ U)

/- Lemma 37.47.4 (2): the local-ring map of a finite morphism at a point that is alone in its
fiber is finite. -/
@[stacks 05B8]
#check (AlgebraicGeometry.IsFinite.stalkMap_finite_of_fiber_eq_singleton :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (h_fiber : f ⁻¹' {f x} = {x}),
    (f.stalkMap x).hom.Finite)

/- Lemma 37.47.4 (3): under finite presentation, the local-ring map at a point that is alone
in its fiber is finitely presented. -/
@[stacks 05B8]
#check (AlgebraicGeometry.IsFinite.stalkMap_finitePresentation_of_fiber_eq_singleton :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Scheme.Hom.FinitePresentation f]
    (x : X) (h_fiber : f ⁻¹' {f x} = {x}),
    (f.stalkMap x).hom.FinitePresentation)

/- Lemma 37.47.4 (4): for a quasicoherent module and a point that is alone in its fiber, the
canonical map from the pushforward stalk to the original stalk is an isomorphism after
restriction of scalars along the local-ring map. -/
@[stacks 05B8]
#check (AlgebraicGeometry.IsFinite.stalkPushforward_isIso_of_fiber_eq_singleton :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (h_fiber : f ⁻¹' {f x} = {x}) (ℱ : X.Modules) [ℱ.IsQuasicoherent],
    IsIso (Scheme.Modules.stalkPushforward f ℱ x))
