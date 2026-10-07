module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Noetherian
import StacksCheckRecall

/-!
# Lemma 29.21.9

Over a locally Noetherian base, finite type is finite presentation.

@stack 01TX
-/

@[expose] public section

universe u

/- Lemma 29.21.9 (1): over a locally Noetherian base, a locally finite type morphism is locally
of finite presentation. -/
@[stacks 01TX]
#check
  (AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.IsLocallyNoetherian S],
      AlgebraicGeometry.LocallyOfFiniteType f →
        AlgebraicGeometry.LocallyOfFinitePresentation f)

/- Lemma 29.21.9 (2): over a locally Noetherian base, a finite type morphism is of finite
presentation. -/
@[stacks 01TX]
#check
  (AlgebraicGeometry.Scheme.Hom.finitePresentation_of_finiteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      [AlgebraicGeometry.IsLocallyNoetherian S],
      AlgebraicGeometry.Scheme.Hom.FinitePresentation f)
