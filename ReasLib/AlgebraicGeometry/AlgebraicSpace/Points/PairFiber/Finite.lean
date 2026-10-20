module

public import Mathlib.Data.Finite.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.PairFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/-- In a cartesian square of algebraic spaces over a scheme, the pair-fibre
over compatible points is finite if the morphism from the first target to the
common target is of finite type and quasi-finite at the first point. -/
theorem fibre_finite_of_finiteType_quasiFiniteAt
    {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback p q f g) [FiniteType f] (x : Points X) (z : Points Z)
    (hx : QuasiFiniteAt f x) (hy : map f x = map g z) :
    (fibre p q x z).Finite :=
  sorry

/-- In a cartesian square of algebraic spaces over a scheme, the pair-fibre
over compatible points is finite if their common image has a monomorphic
field-valued representative and the second morphism is quasi-finite at the
second point. -/
@[stacks 0AC7]
theorem fibre_finite_of_mono_quasiFiniteAt
    {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback q p g f) (x : Points X) (z : Points Z) (y : Points Y)
    (hx : map f x = y) (hz : map g z = y) (η : FieldValuedPoint Y)
    [Mono η.hom] (hη : mk η = y) (hg : QuasiFiniteAt g z) :
    (fibre p q x z).Finite :=
  sorry

/-- In a cartesian square of algebraic spaces over a scheme, the pair-fibre
over compatible points is finite if the common target is decent and the
second morphism is étale. -/
@[stacks 0AC7]
theorem fibre_finite_of_isDecent_etale
    {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback q p g f) (x : Points X) (z : Points Z)
    (hy : map f x = map g z) [IsDecent Y] [Etale g] :
    (fibre p q x z).Finite :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Points
