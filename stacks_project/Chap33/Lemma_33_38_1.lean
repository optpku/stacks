module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 33.38.1: positive higher direct images of quasi-coherent modules along retrocompact
open immersions into locally Noetherian schemes of stalk dimension at most one vanish. -/
@[stacks 09N8] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.isZero_of_quasiCompact_open_of_stalk_ringKrullDim_le_one :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X],
      (∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1) →
      ∀ (U : X.Opens) [QuasiCompact U.ι]
        (ℱ : (U : Scheme).Modules) [ℱ.IsQuasicoherent]
        (p : ℕ), 0 < p →
        IsZero (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule U.ι.toShHom ℱ p))
