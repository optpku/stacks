module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Pushouts of elementary distinguished squares

An elementary distinguished square of algebraic spaces over a scheme is a pushout.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

/-- A pullback square of an elementary distinguished pair of morphisms of algebraic
spaces over a scheme is a pushout. -/
theorem isPushout {S : Scheme.{u}} {P U V W : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) {pU : P ⟶ U} {pV : P ⟶ V}
    [IsElementaryDistinguishedSquare j f] (h : IsPullback pU pV j f) :
    IsPushout pU pV j f :=
  sorry

/-- The canonical fibre-product square of an elementary distinguished pair of morphisms
of algebraic spaces over a scheme is a pushout. -/
theorem isPushout_pullback {S : Scheme.{u}} {U V W : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) [IsElementaryDistinguishedSquare j f] :
    IsPushout (pullback.fst j f) (pullback.snd j f) j f :=
  isPushout j f (CategoryTheory.IsPullback.of_hasPullback j f)

end AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
