/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import stacks_project.Chap76.Lemma_76_15_13_ConormalSequence
public import stacks_project.Chap76.Lemma_76_19_2_FormallySmooth

/-!
# Short exactness of the unramified conormal sequence under formal smoothness

If `h : Z ⟶ X` is formally unramified over `B` and `Z` is formally smooth over
`B`, the canonical right-exact conormal sequence of Lemma 76.15.13 is short
exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
namespace Differentials

variable {S : Scheme.{u}} {B X Z Z' : AlgebraicSpace S}
variable (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
variable [IsUniversalFirstOrder i h'] [FormallyUnramified h]
variable [FormallySmooth (h ≫ f)]
variable (w : i ≫ h' = h)

/-- Lemma 76.19.13: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `h : Z ⟶ X` be a formally unramified morphism of algebraic spaces over `B`.
Assume that `Z` is formally smooth over `B`. Then the canonical exact sequence
`0 ⟶ C_{Z/X} ⟶ h^* Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0` of Lemma 76.15.13 is short exact. -/
@[stacks 06BJ]
theorem shortExact_of_formallySmooth :
    (complex i h' h f w).ShortExact :=
  sorry

/-- For a formally unramified morphism `h : Z ⟶ X` with `Z` formally smooth over
`B`, the first arrow `conormalMap` of the Lemma 76.15.13 sequence is a
monomorphism. -/
instance mono_conormalMap : Mono (conormalMap i h' h f w) :=
  sorry

end Differentials
end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
