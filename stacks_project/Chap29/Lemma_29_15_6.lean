module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.15.6 (1): a morphism locally of finite type over a locally Noetherian scheme has
locally Noetherian source. -/
@[stacks 01T6] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S],
      IsLocallyNoetherian X)

/- Lemma 29.15.6 (2): a finite type morphism over a Noetherian scheme has Noetherian source. -/
@[stacks 01T6] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.isNoetherian :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsNoetherian S],
      IsNoetherian X)
