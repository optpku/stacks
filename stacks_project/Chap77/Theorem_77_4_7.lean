/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Defs.Filter
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Checking relative flatness at associated points of a fibre

For a locally finite-type morphism of algebraic spaces and a finite-type quasicoherent
module, relative flatness at a point follows from relative flatness at the relatively
weakly associated points of the set-theoretic fibre that specialize to it. The converse
holds when the source and target are decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Theorem 77.4.7 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite type. Let `ℱ` be a quasi-coherent `𝒪_X`-module
of finite type. Let `x ∈ |X|` with image `y = Points.map f x ∈ |Y|`, and write
`F = Points.map f ⁻¹' {y} ⊂ |X|` for the set-theoretic fibre. If `ℱ` is flat over `Y` at
every point of `F ∩ relativeWeakAss f ℱ` that specializes to `x`, then `ℱ` is flat at `x`
over `Y`. Under locally of finite type, `Ass_{X/Y}(ℱ)` agrees with `relativeWeakAss f ℱ`. -/
@[stacks 0CWL]
theorem flatOverAt_of_relativeWeakAss_specializingTo
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (x : Points X)
    (h : ∀ x' ∈ relativeWeakAss f ℱ ∩ Points.map f ⁻¹' {Points.map f x},
      Specializes x' x → flatOverAt ℱ f x') :
    flatOverAt ℱ f x :=
  sorry

/-- Theorem 77.4.7 (2): In the same situation, if `X` and `Y` are decent, then flatness of
`ℱ` at `x` over `Y` implies that `ℱ` is flat over `Y` at every `x'` in
`F ∩ relativeWeakAss f ℱ` that specializes to `x`. -/
@[stacks 0CWL]
theorem relativeWeakAss_specializingTo_of_flatOverAt
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    {x x' : Points X} (hflat : flatOverAt ℱ f x)
    (hx'_ass_fiber : x' ∈ relativeWeakAss f ℱ ∩ Points.map f ⁻¹' {Points.map f x})
    (hspec : Specializes x' x) :
    flatOverAt ℱ f x' :=
  sorry

/-- If `X` and `Y` are decent, a finite-type quasicoherent module is flat over `Y` at `x`
if and only if it is flat at every point of the set-theoretic fibre over
`Points.map f x` that lies in `relativeWeakAss f ℱ` and specializes to `x`. -/
theorem flatOverAt_iff_relativeWeakAss_specializingTo
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (x : Points X) :
    flatOverAt ℱ f x ↔
      ∀ x' ∈ relativeWeakAss f ℱ ∩ Points.map f ⁻¹' {Points.map f x},
        Specializes x' x → flatOverAt ℱ f x' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
