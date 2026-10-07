module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Lemma 70.15.4

An integral morphism of algebraic spaces that is bijective on points detects
whether the source and target are schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsScheme

/-- Lemma 70.15.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is integral and `Points.map f : Points X → Points Y`
is bijective, then `X` is a scheme if and only if `Y` is a scheme. -/
@[stacks 07VV]
theorem iff_of_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] (hf : Function.Bijective (Points.map f)) :
    IsScheme X ↔ IsScheme Y :=
  sorry

/-- If `f : X ⟶ Y` is integral and bijective on points, and `Y` is a scheme,
then `X` is a scheme. -/
theorem of_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] (hf : Function.Bijective (Points.map f))
    [IsScheme Y] : IsScheme X :=
  sorry

/-- If `f : X ⟶ Y` is integral and bijective on points, and `X` is a scheme,
then `Y` is a scheme. -/
theorem of_isIntegralHom_of_isScheme {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] (hf : Function.Bijective (Points.map f))
    [IsScheme X] : IsScheme Y :=
  sorry

end IsScheme

end AlgebraicGeometry.AlgebraicSpace
