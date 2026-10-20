module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GenericFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/- Lemma 37.24.8: after restricting a finite-type morphism to an irreducible base to a
nonempty open, there is a surjective finite étale cover by an irreducible affine scheme such
that every irreducible component of the generic fibre of the resulting base change is
geometrically irreducible. -/
@[stacks 0551] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_finiteEtaleCover_geometricallyIrreducibleGenericFiber :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y],
      ∃ (V : Y.Opens) (_ : Nonempty V) (Y' : Scheme.{u}) (g : Y' ⟶ V)
        (_ : Surjective g) (_ : IsFinite g) (_ : Etale g)
        (_ : IsAffine Y') (_ : IrreducibleSpace Y'),
        GeometricallyIrreducible.Components.all
          ((Limits.pullback.fst g (Limits.pullback.fst V.ι f)).fiberToSpecResidueField
            (genericPoint Y')))

end AlgebraicGeometry.Scheme.Hom.FiniteType
