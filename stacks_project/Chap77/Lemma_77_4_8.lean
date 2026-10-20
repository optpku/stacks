/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Defs.Filter
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Lemma 77.4.8

On a locally finite-type algebraic space over a local scheme, a finite-type
quasi-coherent module that is flat along the closed fibre, and whose relative
assassin specializes into that fibre, is flat over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace relativeAssassin

/-- Lemma 77.4.8: Let `S` be a local scheme with closed point `s`. Let
`f : X ⟶ S` be a morphism from an algebraic space `X` to `S` which is locally
of finite type. Let `ℱ` be a finite type quasi-coherent `𝒪_X`-module. Assume
that every point of `Ass_{X/S}(ℱ)` specializes to a point of the closed fibre
`X_s`, and that `ℱ` is flat over `S` at every point of `X_s`. Then `ℱ` is
flat over `S`.
Here `f` is `toBase X`, `Ass_{X/S}(ℱ)` is `relativeAssassin (toBase X) ℱ`,
and `|X_s|` is `{z | Points.base z = s}`. The closed point is identified by
`S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)`. Flatness over `S` is
the pointwise condition `flatOverAt ℱ (toBase X)`. The specialization
assumption holds, for example, if `f` is of finite type and `ℱ` is pure
along `X_s`, or if `f` is proper. -/
@[stacks 0CWM]
theorem flatOver_of_specializesTo_closedFiber
    {S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] {X : AlgebraicSpace S}
    [LocallyOfFiniteType (toBase X)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (h_ass : ∀ x ∈ relativeAssassin (toBase X) ℱ,
      ∃ z : Points X, Points.base z = s ∧ Specializes x z)
    (h_flat : ∀ z : Points X, Points.base z = s → flatOverAt ℱ (toBase X) z) :
    ∀ x : Points X, flatOverAt ℱ (toBase X) x :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
