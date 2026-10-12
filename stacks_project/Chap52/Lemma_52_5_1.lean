/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.LocalCohomology.Artinian
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Artinian

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 52.5.1 (1): every local cohomology module of a finite module over a
Noetherian local ring satisfies the descending chain condition. -/
@[stacks 0DX0] #check (localCohomology.instIsArtinianMaximalIdeal :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [Module.Finite A M] (i : ℕ),
    IsArtinian A ((localCohomology (IsLocalRing.maximalIdeal A) i).obj M))

/- Lemma 52.5.1 (2): positive-degree cohomology of a coherent module on the
punctured spectrum of a Noetherian local ring satisfies the descending chain condition
as an `A`-module through the punctured-spectrum inclusion. -/
@[stacks 0DX0] #check (AlgebraicGeometry.PuncturedSpectrum.instIsArtinianCohomologySucc :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (F : (PuncturedSpectrum.scheme A).Modules) [F.IsCoherent] (i : ℕ),
    IsArtinian A
      (Scheme.Hom.cohomology (PuncturedSpectrum.puncturedOpen A).ι F (i + 1)))
