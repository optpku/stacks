module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Blowup
import StacksCheckRecall

/-!
# Finite locally free morphisms of algebraic spaces after admissible blowups

A proper morphism of algebraic spaces that is finite locally free over a
quasi-compact open of a qcqs base becomes finite locally free after a
`U`-admissible blowup, on the strict transform.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.39.2: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. Let `U ⊂ B` be an open subspace. Assume `B` is
quasi-compact and quasi-separated, `U` is quasi-compact, `f : X ⟶ B` is proper,
and `f⁻¹(U) ⟶ U` is finite locally free. Then there exists a `U`-admissible
blowup `B' ⟶ B` such that the strict transform `X'` of `X` is finite locally
free over `B'`. -/
@[stacks 0B4K] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_finiteLocallyFree :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [Proper f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [FiniteLocallyFree (pullback.snd f U.ι)],
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        FiniteLocallyFree (strictTransformSnd b (Z.inverseImageSubspace b) f))

end AlgebraicGeometry.AlgebraicSpace
