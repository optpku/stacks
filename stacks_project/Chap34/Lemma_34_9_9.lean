module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Refinement
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

/- Lemma 34.9.9: every fpqc cover of an affine scheme admits a finite affine
standard refinement whose component maps into the original cover are open
immersions. -/
@[stacks 022E] #check
  (AlgebraicGeometry.FpqcCover.exists_standardRefinement :
    ∀ {T : Scheme.{u}} [IsAffine T] (𝒰 : FpqcCover.{u, v} T),
      ∃ 𝒱 : StandardFpqcCover T,
        ∃ φ : SemiRepresentableFamily.Over.Hom 𝒱.toOverFamily (ofArrows 𝒰.X 𝒰.f),
          ∀ j : Fin 𝒱.n, IsOpenImmersion ((φ.f j).left))
