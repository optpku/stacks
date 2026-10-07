module

public import Mathlib.Data.Finite.Defs
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap68.Lemma_68_18_6_Fibre

/-!
# Finite neighbourhoods of finite geometric fibres of proper morphisms

A proper morphism of algebraic spaces over a locally Noetherian target whose
geometric fibre over a geometric point is finite is finite over some open
neighbourhood of that geometric point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.23.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `ybar` be a geometric point of `Y`. Assume `Y`
is locally Noetherian, `f` is proper, and `|X_ybar|` is finite. Then there
exists an open neighbourhood `V ⊂ Y` of `ybar` such that
`openInverseImageTo f ι : openInverseImage f ι ⟶ V` is finite.

The open neighbourhood is an open immersion `ι : V ⟶ Y` with
`ybar.image ∈ Set.range (Points.map ι)`, the restricted morphism is
`openInverseImageTo f ι`, and finiteness of `|X_ybar|` is
`Finite (Points (fieldFiber f ybar.toFieldValuedPoint))`. A more general
version without local Noetherianity, using quasi-finiteness at ordinary
points over `y`, is Lemma 76.35.2. -/
@[stacks 0A4W]
theorem exists_isFinite_openInverseImageTo_of_finite_fieldFiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Proper f] (ybar : GeometricPoint Y)
    (hfin : Finite (Points (fieldFiber f ybar.toFieldValuedPoint))) :
    ∃ (V : AlgebraicSpace S) (ι : V ⟶ Y) (hι : IsOpenImmersion ι),
      ybar.image ∈ Set.range (Points.map ι) ∧
        IsFinite (openInverseImageTo f ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
