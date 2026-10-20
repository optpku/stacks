module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianSquare
import StacksCheckRecall

/-!
# Lemma 81.6.4

In a commutative diagram of algebraic spaces, if the left and outer squares
are cartesian and the bottom-left map is surjective étale, then the right
square is cartesian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 81.6.4: Let `S` be a scheme. Let `A ⟶ C ⟶ E` over `B ⟶ D ⟶ F` be a
commutative diagram of algebraic spaces over `S`. If the left square `A, B, C, D`
and the outer square `A, B, E, F` are cartesian and `B ⟶ D` is surjective étale,
then the right square `C, D, E, F` is cartesian. -/
@[stacks 07VZ] #check
  (AlgebraicGeometry.AlgebraicSpace.isPullback_of_left_of_surjective_etale :
    ∀ {S : Scheme.{u}} {A B C D E F : AlgebraicSpace S}
    {fAC : A ⟶ C} {fAB : A ⟶ B} {fCD : C ⟶ D} {fBD : B ⟶ D}
    {fCE : C ⟶ E} {fEF : E ⟶ F} {fDF : D ⟶ F}
    (hABCD : IsPullback fAC fAB fCD fBD)
    (hABEF : IsPullback (fAC ≫ fCE) fAB fEF (fBD ≫ fDF))
    (wCDEF : fCE ≫ fEF = fCD ≫ fDF) [Surjective fBD] [Etale fBD],
    IsPullback fCE fCD fEF fDF)

end AlgebraicGeometry.AlgebraicSpace
