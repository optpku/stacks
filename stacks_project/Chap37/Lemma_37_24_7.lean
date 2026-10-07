module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GenericFiber

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.24.7: after restricting a finite-type morphism to an irreducible base to a
nonempty open, there is a finite universal homeomorphism from an integral affine scheme such
that the reduced pullback is flat and finitely presented with geometrically reduced generic
fibre; its map to the restricted source is also finite and a universal homeomorphism. -/
@[stacks 0550]
#check (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_finiteUniversalHomeomorphism_geometricallyReducedGenericFiber :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FiniteType f] [IrreducibleSpace Y],
    ∃ (V : Y.Opens) (_ : Nonempty V) (Y' : Scheme.{u}) (g : Y' ⟶ V)
      (_ : IsFinite g) (_ : UniversalHomeomorphism g) (_ : IsIntegral Y') (_ : IsAffine Y'),
      let X_V := pullback V.ι f
      let pV : X_V ⟶ V := pullback.fst V.ι f
      let jV : X_V ⟶ X := pullback.snd V.ι f
      let P := pullback g pV
      let X' := Scheme.reduction P
      let f' : X' ⟶ Y' := Scheme.reductionι P ≫ pullback.fst g pV
      let g' : X' ⟶ X_V := Scheme.reductionι P ≫ pullback.snd g pV
      ∃ (_ : CommSq jV pV f V.ι) (_ : CommSq g' f' pV g)
        (_ : IsFinite g') (_ : UniversalHomeomorphism g') (_ : Flat f')
        (_ : Scheme.Hom.FinitePresentation f'),
        GeometricallyReduced (f'.fiberToSpecResidueField (genericPoint Y')))
