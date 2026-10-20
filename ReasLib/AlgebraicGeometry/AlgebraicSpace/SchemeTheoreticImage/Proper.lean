module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage

/-!
# Scheme-theoretic images of proper morphisms of algebraic spaces

In a commutative triangle of algebraic spaces over a scheme, if the first
leg is proper and the second is separated and locally of finite type, then
the scheme-theoretic image is proper over the base and the comparison from
the source is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/-- In a commutative triangle of algebraic spaces over a scheme, if the source
is proper over the base and the target is separated and locally of finite type
over the base, the comparison to the scheme-theoretic image is surjective. -/
theorem surjective_toImage {S : Scheme.{u}} {X Y B Z : AlgebraicSpace S}
    (h : X ⟶ Y) (f : X ⟶ B) (g : Y ⟶ B) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (hcomm : h ≫ g = f) [Proper f] [Separated g] [LocallyOfFiniteType g]
    [IsSchemeTheoreticImage h toImage ι] : Surjective toImage :=
  sorry

/-- In a commutative triangle of algebraic spaces over a scheme, if the source
is proper over the base and the target is separated and locally of finite type
over the base, the scheme-theoretic image is proper over the base. -/
theorem proper_comp {S : Scheme.{u}} {X Y B Z : AlgebraicSpace S}
    (h : X ⟶ Y) (f : X ⟶ B) (g : Y ⟶ B) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (hcomm : h ≫ g = f) [Proper f] [Separated g] [LocallyOfFiniteType g]
    [IsSchemeTheoreticImage h toImage ι] : Proper (ι ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
