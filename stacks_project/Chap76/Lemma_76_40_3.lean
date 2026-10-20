/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Chow.Noetherian
import StacksCheckRecall

/-!
# Chow embeddings over a Noetherian algebraic space

A separated finite-type morphism of algebraic spaces into a Noetherian algebraic
space admits a dense open on the source that, after a `U`-admissible blowup,
opens into a proper representable space obtained by blowing up a closed subspace
of a relative projective space.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.40.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is separated and of finite type, and
`Y` is Noetherian. Then there exists a dense open subspace `U ⊂ X` and a
commutative diagram in which the arrows with source `U.X` are open immersions,
`X' ⟶ X` is a `U`-admissible blowup, `X' ⟶ Z'` is an open immersion, and
`Z' ⟶ Y` is a proper representable morphism of algebraic spaces. More
precisely, `Z' ⟶ Z` is a `U`-admissible blowup and
`Z ⟶ ProjectiveSpace n Y` is a closed immersion. -/
@[stacks 088S] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_dense_open_isAdmissibleBlowup_closedImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Separated f] [IsNoetherian Y],
    ∃ (U : OpenSubspace X) (n : ℕ) (X' Z' Z : AlgebraicSpace S)
      (bX : X' ⟶ X) (j : X' ⟶ Z') (bZ : Z' ⟶ Z)
      (c : Z ⟶ ProjectiveSpace n Y)
      (ιX' : U.X ⟶ X') (ιZ' : U.X ⟶ Z') (ιZ : U.X ⟶ Z)
      (hιX' : IsOpenImmersion ιX') (hιZ' : IsOpenImmersion ιZ')
      (hιZ : IsOpenImmersion ιZ),
      Dense (U.pointsSet : Set (Points X)) ∧
        IsAdmissibleBlowup U bX ∧ IsOpenImmersion j ∧
        Proper (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) ∧
        yoneda.relativelyRepresentable (bZ ≫ c ≫ ProjectiveSpace.toBase n Y) ∧
        IsAdmissibleBlowup ⟨U.X, ιZ, hιZ⟩ bZ ∧
        IsClosedImmersion c ∧
        ιX' ≫ bX = U.ι ∧ ιX' ≫ j = ιZ' ∧ ιZ' ≫ bZ = ιZ ∧
        ιZ ≫ c ≫ ProjectiveSpace.toBase n Y = U.ι ≫ f ∧
        bX ≫ f = j ≫ bZ ≫ c ≫ ProjectiveSpace.toBase n Y)

end AlgebraicGeometry.AlgebraicSpace
