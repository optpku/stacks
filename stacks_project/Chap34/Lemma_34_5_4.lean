module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth.StandardRefinement
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 34.5.4: a smooth covering of an affine scheme admits a finite affine
refinement by standard smooth morphisms, and the refining affine schemes may
be chosen as open affine subschemes of members of the original covering. -/
@[stacks 0222] #check
  (AlgebraicGeometry.Scheme.SmoothCovering.exists_standardSmoothRefinement :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
      {ι : Type v} {family : ι → CategoryTheory.Over T},
      AlgebraicGeometry.Scheme.SmoothCovering family →
        ∃ 𝒱 : AlgebraicGeometry.StandardSmoothCovering T,
          ∃ φ : CategoryTheory.SemiRepresentableFamily.Over.Hom 𝒱.toOverFamily
              (CategoryTheory.SemiRepresentableFamily.Over.ofArrows
                (fun i : ι ↦ (family i).left) (fun i ↦ (family i).hom)),
            ∀ j : Fin 𝒱.n, AlgebraicGeometry.IsOpenImmersion ((φ.f j).left))
