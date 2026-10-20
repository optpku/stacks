module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Proper.Blowup
import StacksCheckRecall

/-!
# Isomorphisms after admissible blowups of algebraic spaces

A proper morphism of algebraic spaces that is an isomorphism over a
quasi-compact open of a qcqs base becomes an isomorphism after a `U`-admissible
blowup, on the strict transform.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.39.3: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. Let `U ⊂ B` be an open subspace. Assume `B` is
quasi-compact and quasi-separated, `U` is quasi-compact, `f : X ⟶ B` is proper,
and `f⁻¹(U) ⟶ U` is an isomorphism. Then there exists a `U`-admissible blowup
`B' ⟶ B` such that the strict transform `X'` of `X` maps isomorphically to
`B'`. -/
@[stacks 0GUW] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_strictTransform_isIso :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [Proper f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [IsIso (pullback.snd f U.ι)],
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        IsIso (strictTransformSnd b (Z.inverseImageSubspace b) f))

end AlgebraicGeometry.AlgebraicSpace
