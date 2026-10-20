module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Blowup
import StacksCheckRecall

/-!
# Flattening morphisms of algebraic spaces by admissible blowups

A finite-type quasi-separated morphism of algebraic spaces that is flat and
locally of finite presentation over a quasi-compact open of a qcqs base becomes
flat and of finite presentation after a `U`-admissible blowup, on the strict
transform.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 76.39.1: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. Let `U ⊂ B` be an open subspace. Assume `B` is
quasi-compact and quasi-separated, `U` is quasi-compact, `f : X ⟶ B` is of
finite type and quasi-separated, and `f⁻¹(U) ⟶ U` is flat and locally of
finite presentation. Then there exists a `U`-admissible blowup `B' ⟶ B` such
that the strict transform `X'` of `X` is flat and of finite presentation over
`B'`. -/
@[stacks 087E] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_flat_finitePresentation :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [FiniteType f] [QuasiSeparated f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [Flat (pullback.snd f U.ι)]
    [LocallyOfFinitePresentation (pullback.snd f U.ι)],
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        let f' := strictTransformSnd b (Z.inverseImageSubspace b) f
        Flat f' ∧ FinitePresentation f')
