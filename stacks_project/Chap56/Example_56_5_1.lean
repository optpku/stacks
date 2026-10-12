/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u w

/- Example 56.5.1 (1): the Fourier–Mukai functor associated to a quasicoherent
kernel is `R`-linear for the scalar structures induced by the two structure morphisms. -/
@[stacks 0FZB]
#check (AlgebraicGeometry.Scheme.QCoh.fourierMukaiFunctor.linear :
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
    (x : X ⟶ Spec (CommRingCat.of R)) → (y : Y ⟶ Spec (CommRingCat.of R)) →
    [CompactSpace X] → [QuasiSeparatedSpace X] →
    (K : Scheme.QCoh (Limits.pullback x y)) →
    Scheme.QCoh.LinearOver x y (AlgebraicGeometry.Scheme.QCoh.fourierMukaiFunctor x y K))

/- Example 56.5.1 (2): the Fourier–Mukai functor associated to a quasicoherent
kernel preserves arbitrary direct sums. -/
@[stacks 0FZB]
#check (AlgebraicGeometry.Scheme.QCoh.fourierMukaiFunctor.preservesCoproducts :
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
    (x : X ⟶ Spec (CommRingCat.of R)) → (y : Y ⟶ Spec (CommRingCat.of R)) →
    [CompactSpace X] → [QuasiSeparatedSpace X] →
    (K : Scheme.QCoh (Limits.pullback x y)) → (J : Type w) →
    PreservesColimitsOfShape (Discrete J)
      (AlgebraicGeometry.Scheme.QCoh.fourierMukaiFunctor x y K))
