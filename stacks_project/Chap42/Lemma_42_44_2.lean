module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.VectorBundle.ShortExact

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.ChowGroup.AssociatedVectorBundle

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.ShortExact

/- Lemma 42.44.2: for a short exact sequence of finite locally free modules, pushforward
from the subbundle after flat pullback equals pullback after capping with the canonical
top Chern class of the quotient, on every joint clopen rank locus. -/
@[stacks 0FAA] #check
  (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.ShortExact.pushforward_pullback_eq_topChern :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (C : ShortComplex X.left.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
    [C.X₃.IsFiniteLocallyFree] (hC : C.ShortExact) (r₁ r₃ : ℕ)
    (P₁ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra
        (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₁)))
    [Scheme.IsRelativeSpectrumOver P₁]
    (P₂ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra
        (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₂)))
    [Scheme.IsRelativeSpectrumOver P₂]
    (k : ℤ) (α : RelativeChow δ X k),
    pushforward δ (rankPairOver X C r₁ r₃) (rankPairRestriction X C hC r₁ r₃)
        (rankPairRestriction_shortExact X C hC r₁ r₃) r₁ r₃ P₁ P₂
        (k + (r₁ : ℤ))
        (AssociatedVectorBundle.flatPullback δ (rankPairOver X C r₁ r₃)
          (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₁) r₁ P₁ k
          (rankPairPullback δ X C r₁ r₃ k α)) =
      cast (congrArg
        (relativeChow δ (rankPairOver X C r₁ r₃)
          (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₂) P₂)
        (topChernPullbackDegree k r₁ r₃))
        (AssociatedVectorBundle.flatPullback δ (rankPairOver X C r₁ r₃)
          (Scheme.Modules.dual (rankPairRestriction X C hC r₁ r₃).X₂) (r₁ + r₃) P₂ (k - (r₃ : ℤ))
          ((rankPairTopChern δ X (ChernClass.Theory.canonical δ X.hom) C r₁ r₃).cap
            (𝟙 (rankPairOver X C r₁ r₃)) (𝟙 (rankPairOver X C r₁ r₃))
            (𝟙 (rankPairOver X C r₁ r₃)) IsPullback.of_id_snd k
            (rankPairPullback δ X C r₁ r₃ k α))))

end AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.ShortExact
