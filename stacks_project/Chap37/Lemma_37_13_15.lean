module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.BaseChange.Homology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.13.15: for a cartesian square of schemes with `g : Y' ⟶ Y` flat,
the canonical map `(g')^* NL(f) ⟶ NL(f')` is a quasi-isomorphism. -/
@[stacks 0FJZ] #check
  (@AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.map_quasiIso_of_isPullback_of_flat :
    ∀ {X X' Y Y' : AlgebraicGeometry.Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (hpb : IsPullback g' f' f g) [Flat g],
      QuasiIso (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.BaseChange.map hpb.toCommSq))
