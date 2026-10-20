module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.TorAmplitude
import StacksCheckRecall

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

/- Lemma 75.13.8: Let `S` be a scheme. Let `X` be a quasi-separated algebraic
space over `S`. Let `E` be an object of `D_QCoh(𝒪_X)`. Let `a ≤ b`. Then `E`
has tor amplitude in `[a, b]` if and only if for every quasi-coherent
`𝒪_X`-module `F` we have `H^i(E ⊗ᴸ F) = 0` for `i ∉ [a, b]`. -/
@[stacks 08IL] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.hasTorAmplitudeIn_iff_homology :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
      (E : DerivedQCoh X) (a b : ℤ) (hab : a ≤ b),
    DerivedCategory.DerivedTensor.HasTorAmplitudeIn E.obj a b ↔
      ∀ (F : QCoh X) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj
          (E.obj ⊗ᴸ (DerivedCategory.singleFunctor (Modules X) 0).obj F.obj)))
