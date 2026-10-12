/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Characterization
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.13.3: for a scheme morphism, quasi-affineness is equivalent to an affine-cover
criterion, to a quasi-compact open immersion into a relative spectrum, and to the analogous
condition for the canonical morphism into the relative spectrum of the pushforward structure
sheaf. -/
@[stacks 01SM] #check
  (AlgebraicGeometry.quasiAffineHom_tfae :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      List.TFAE [
        AlgebraicGeometry.QuasiAffineHom f,
        ∃ cover : S.AffineOpenCover,
          ∀ i : cover.I₀, ((cover.openCover.pullback₁ f).X i).IsQuasiAffine,
        ∃ (A : S.QcAlgebraUnder)
            (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
          AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P ∧
            ∃ j : X ⟶ AlgebraicGeometry.Scheme.relativeSpec P,
              AlgebraicGeometry.QuasiCompact j ∧ AlgebraicGeometry.IsOpenImmersion j ∧
                j ≫ AlgebraicGeometry.Scheme.relativeSpecπ P = f,
        AlgebraicGeometry.HasQuasiCompactOpenImmersionToPushforwardRelativeSpectrum f])
