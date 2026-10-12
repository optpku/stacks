/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.StrictTransform
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 38.33.5: the scheme-theoretic image of the canonical lift of a quasi-compact
morphism to `X' ×_S Y` is the strict transform of its image in `X ×_S Y`, compatibly with
the two closed immersions into `X' ×_S Y`. -/
@[stacks 0F3Y] #check
  (AlgebraicGeometry.Scheme.Hom.image_liftAdmissible_isomorphic_strictTransform :
    ∀ {S X Y V X' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
      (q : V ⟶ pullback f g) [QuasiCompact q]
      (U : X.Opens) (b : X' ⟶ X) (I : X.IdealSheafData)
      [IsAdmissibleBlowupCenter U b I]
      (hU : Set.range (q ≫ pullback.fst f g).base ⊆ Set.range U.ι.base),
      Nonempty
        (Over.mk
            (AlgebraicGeometry.Scheme.Hom.liftAdmissiblePullback f g q U b I hU).imageι ≅
          Over.mk (AlgebraicGeometry.Scheme.Hom.strictTransformImageMap f g q b I)))
