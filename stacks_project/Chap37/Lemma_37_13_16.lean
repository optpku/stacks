module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.BaseChange.Derived
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.13.16 (1): for a cartesian square of schemes with `f` flat, the canonical
map from the ordinary pullback of `NL(f)` to `NL(f')` is a quasi-isomorphism. -/
@[stacks 0FK0] #check
  (@AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.underivedComparison_isIso_of_flat :
    ∀ {X X' Y Y' : _root_.AlgebraicGeometry.Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (hcart : IsPullback g' f' f g) [Flat f],
      IsIso
        (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.underivedComparison
          hcart.toCommSq))

/- Lemma 37.13.16 (2): if moreover `NL(f)` has Tor-amplitude in `[-1, 0]`, the canonical
map from its derived pullback to `NL(f')` is an isomorphism in the derived category. -/
@[stacks 0FK0] #check
  (@AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.derivedComparison_isIso_of_flat_of_hasTorAmplitudeIn :
    ∀ {X X' Y Y' : _root_.AlgebraicGeometry.Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (hcart : IsPullback g' f' f g) [Flat f]
      [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
      (hNL : RingedSpace.HasTorAmplitudeIn
        (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0),
      IsIso
        (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.derivedComparison
          hcart.toCommSq))
