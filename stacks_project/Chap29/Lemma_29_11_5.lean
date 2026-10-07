module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Equivalence

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.11.5 (1): affine morphisms over a scheme are anti-equivalent to
quasi-coherent algebras by pushforward of structure sheaves. -/
@[stacks 01SA] #check
  (AlgebraicGeometry.AffineMorphismOver.exists_pushforwardEquivalence :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      ∃ e : (AlgebraicGeometry.AffineMorphismOver S)ᵒᵖ ≌
          AlgebraicGeometry.Scheme.QcAlgebraUnder S,
        AlgebraicGeometry.AffineMorphismOver.IsPushforwardEquivalence S e)

/- Lemma 29.11.5 (2): the anti-equivalence is compatible with arbitrary base
change on both affine morphisms and quasi-coherent algebras. -/
@[stacks 01SA] #check
  (AlgebraicGeometry.AffineMorphismOver.exists_baseChangeCompatiblePushforwardEquivalence :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      ∃ eS : (AlgebraicGeometry.AffineMorphismOver S)ᵒᵖ ≌
          AlgebraicGeometry.Scheme.QcAlgebraUnder S,
        AlgebraicGeometry.AffineMorphismOver.IsPushforwardEquivalence S eS ∧
          ∀ {S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S),
            ∃ (eS' : (AlgebraicGeometry.AffineMorphismOver S')ᵒᵖ ≌
                AlgebraicGeometry.Scheme.QcAlgebraUnder S')
              (F : AlgebraicGeometry.Scheme.QcAlgebraUnder S ⥤
                AlgebraicGeometry.Scheme.QcAlgebraUnder S')
              (_ : ∀ A,
                AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A (F.obj A)),
              AlgebraicGeometry.AffineMorphismOver.IsPushforwardEquivalence S' eS' ∧
                Nonempty
                  ((AlgebraicGeometry.AffineMorphismOver.baseChange g).op ⋙ eS'.functor ≅
                    eS.functor ⋙ F))
