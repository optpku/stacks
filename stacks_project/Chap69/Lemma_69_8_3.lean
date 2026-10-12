/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap69.Situation_69_16_1_Cohomology

/-!
# Lemma 69.8.3

Étale cohomology of a quasi-coherent module is preserved by pushforward along an affine
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.8.3: let `S` be a scheme. Let `f : X ⟶ Y` be an affine morphism of algebraic
spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Then `H^i(X, F)` is isomorphic
to `H^i(Y, f_* F)` for all `i ≥ 0`. -/
@[stacks 0D2U]
theorem cohomology_iso_pushforward_of_affine
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    IsIsomorphic (cohomology X F i) (cohomology Y ((Modules.pushforward f).obj F) i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
