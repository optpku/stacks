/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap69.Definition_69_12_1_Instances

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 69.13.1: if `X` is a Noetherian algebraic space over a scheme `S` and `F` is a
coherent `𝒪_X`-module, then every ascending `ℕ`-indexed chain of quasi-coherent submodules
of `F` is eventually constant. -/
@[stacks 07UJ]
theorem quasiCoherentSubobject_monotone_stabilizes
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (f : ℕ →o Subobject F)
    (hf_qc : ∀ n : ℕ, (((f n : Subobject F) : X.Modules)).IsQuasicoherent) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
