module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FlatClosedImmersion
import StacksCheckRecall

/-!
# Lemma 29.26.2

Flat closed immersions of finite presentation.

@stack 0819
-/

@[expose] public section

universe u

/- Lemma 29.26.2: A flat closed immersion of finite presentation is an open immersion. -/
@[stacks 0819] #check
  (AlgebraicGeometry.isOpenImmersion_of_isClosedImmersion :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y},
      AlgebraicGeometry.IsClosedImmersion f →
        ∀ [AlgebraicGeometry.Flat f]
          [AlgebraicGeometry.Scheme.Hom.FinitePresentation f],
          AlgebraicGeometry.IsOpenImmersion f)

#check
  (AlgebraicGeometry.isClopen_range_of_flat_closedImmersion :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y},
      AlgebraicGeometry.IsClosedImmersion f →
        ∀ [AlgebraicGeometry.Flat f]
          [AlgebraicGeometry.Scheme.Hom.FinitePresentation f],
          IsOpen (Set.range f.base) ∧ IsClosed (Set.range f.base))
