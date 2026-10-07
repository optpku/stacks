module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Fpqc
import StacksCheckRecall

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.DescentData.Pullback

variable {S : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S}
variable {𝒱 : SemiRepresentableFamily.Over.{w} S}

/- Lemma 35.35.11 (1): pullback of scheme descent data along a refinement between fpqc
covering families is fully faithful. -/
@[stacks 02W0] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.fullyFaithfulOfFpqcRefinement :
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map (𝟙 S)) 𝒰) 𝒱) →
    (h𝒰 : Scheme.FpqcCovering 𝒰.obj) → (h𝒱 : Scheme.FpqcCovering 𝒱.obj) →
    Nonempty (functorOfHom φ).FullyFaithful)

end AlgebraicGeometry.Scheme.DescentData.Pullback

namespace AlgebraicGeometry.Scheme.DescentData

variable {S : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S}

/- Lemma 35.35.11 (2): restriction from schemes over `S` to descent data for any fpqc
covering family of `S` is fully faithful. -/
@[stacks 02W0]
#check
  (AlgebraicGeometry.Scheme.DescentData.fullyFaithfulOfFpqcCover :
    (h𝒰 : Scheme.FpqcCovering 𝒰.obj) →
    Nonempty (Scheme.overPseudofunctor.toDescentData
      (fun i : 𝒰.index ↦ (𝒰.obj i).hom)).FullyFaithful)

end AlgebraicGeometry.Scheme.DescentData
