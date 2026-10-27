/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Local
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlong
open IsLocalRing

universe u

/- Lemma 88.30.4: Let `(A, maximalIdeal A)` be a Noetherian local ring. Let
`f : X ⟶ S` be an object of 88.30.0.1 such that `f` is proper. Then there
exists a `U`-admissible blowup `S' ⟶ S` which dominates `X`. Here `S` is
`specOver hA`, an object of 88.30.0.1 is
`Y : Source (specOver hA) (zeroLocusPoints hA (maximalIdeal A))`, `X` is
`Y.obj.left`, `f` is `Y.obj.hom`, and `U = maximalIdealComplement hA`. A
`U`-admissible blowup is `AlgebraicSpace.IsAdmissibleBlowup (maximalIdealComplement hA) b`.
Domination means there is a factorization `S' ⟶ X ⟶ S` of the blowup morphism,
i.e. `g ≫ Y.obj.hom = b`. This is the special case of Lemma 76.39.5 for a
Noetherian local affine base. -/
@[stacks 0AE6] #check
  (AlgebraicGeometry.AlgebraicSpace.completionAlong.exists_isAdmissibleBlowup_dominating :
    ∀ {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S)
    (Y : Source (specOver hA) (zeroLocusPoints hA (maximalIdeal A)))
    [Proper Y.obj.hom],
    ∃ (S' : AlgebraicSpace S) (b : S' ⟶ specOver hA) (g : S' ⟶ Y.obj.left),
      AlgebraicGeometry.AlgebraicSpace.IsAdmissibleBlowup (maximalIdealComplement hA) b ∧
        g ≫ Y.obj.hom = b)
