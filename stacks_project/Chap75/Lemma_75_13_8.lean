/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_5_6_Instances

/-!
# Lemma 75.13.8

On a quasi-separated algebraic space, an object of `D_QCoh(𝒪_X)` has
Tor-amplitude in `[a, b]` if and only if its derived tensor product with every
quasi-coherent `𝒪_X`-module has vanishing cohomology outside that interval.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.13.8: Let `S` be a scheme. Let `X` be a quasi-separated algebraic
space over `S`. Let `E` be an object of `D_QCoh(𝒪_X)`. Let `a ≤ b`. Then `E`
has tor amplitude in `[a, b]` if and only if for every quasi-coherent
`𝒪_X`-module `F` we have `H^i(E ⊗ᴸ F) = 0` for `i ∉ [a, b]`. -/
@[stacks 08IL]
theorem hasTorAmplitudeIn_iff_homology {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiSeparated X] (E : DerivedQCoh X) (a b : ℤ) (hab : a ≤ b) :
    DerivedCategory.DerivedTensor.HasTorAmplitudeIn E.obj a b ↔
      ∀ (F : QCoh X) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj
          (E.obj ⊗ᴸ (DerivedCategory.singleFunctor (Modules X) 0).obj F.obj)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
