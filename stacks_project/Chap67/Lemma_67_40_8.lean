module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage

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

/-- Lemma 67.40.8 (1): Let `S` be a scheme, and let `h : X ⟶ Y`, `f : X ⟶ B`,
`g : Y ⟶ B` be a commutative triangle of morphisms of algebraic spaces over
`S`. If `f` is proper and `g` is separated and locally of finite type, then
the scheme-theoretic image of `h` is proper over `B`. -/
@[stacks 0AGD]
theorem proper_comp {S : Scheme.{u}} {X Y B Z : AlgebraicSpace S}
    (h : X ⟶ Y) (f : X ⟶ B) (g : Y ⟶ B) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (hcomm : h ≫ g = f) [Proper f] [Separated g] [LocallyOfFiniteType g]
    [IsSchemeTheoreticImage h toImage ι] : Proper (ι ≫ g) :=
  sorry

/-- Lemma 67.40.8 (2): Let `S` be a scheme, and let `h : X ⟶ Y`, `f : X ⟶ B`,
`g : Y ⟶ B` be a commutative triangle of morphisms of algebraic spaces over
`S`. If `f` is proper and `g` is separated and locally of finite type, then
the comparison from `X` to the scheme-theoretic image of `h` is surjective. -/
@[stacks 0AGD]
theorem surjective_toImage {S : Scheme.{u}} {X Y B Z : AlgebraicSpace S}
    (h : X ⟶ Y) (f : X ⟶ B) (g : Y ⟶ B) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (hcomm : h ≫ g = f) [Proper f] [Separated g] [LocallyOfFiniteType g]
    [IsSchemeTheoreticImage h toImage ι] : Surjective toImage :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
