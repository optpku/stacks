module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import stacks_project.Chap101.Lemma_101_36_4_Etale
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Remark_101_19_5_AutomorphismGroup
public import stacks_project.Chap106.Theorem_106_13_9_Keel_Mori

/-!
# Cartesian squares of Keel–Mori moduli spaces

An étale separated morphism of algebraic stacks that induces isomorphisms on
automorphism groups, with finite inertia on the target, fits in a 2-cartesian
square whose vertical arrows are the uniform categorical moduli spaces of
Theorem 106.13.9 and whose bottom arrow is a separated étale morphism of
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.13.10. Let `h : X' ⟶ X` be a morphism of algebraic stacks.
Assume the inertia morphism `forget X : I_X ⟶ X` is finite, `h` is étale,
`h` is separated, and `h` induces isomorphisms on automorphism groups at
every point of `|X'|` (Remark 101.19.5). If `f : X ⟶ M.toGroupoids` is a
uniform categorical moduli space as in Theorem 106.13.9, then there exist an
algebraic space `M'`, a uniform categorical moduli space
`f' : X' ⟶ M'.toGroupoids`, a separated étale morphism `g : M' ⟶ M` of
algebraic spaces, and a 2-cell making the displayed square cartesian. -/
@[stacks 0DUV]
theorem exists_cartesian_separated_etale_moduliSpace
    {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X']
    [IsFinite (forget.{u + 1, u, u, u + 1} X)]
    (h : X' ⟶ X) [Etale h] [Separated h]
    (h_isoAt : ∀ x : |X'|, automorphismGroup.IsIsoAt h x)
    {M : AlgebraicSpace S} (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpace f] :
    ∃ (M' : AlgebraicSpace S) (f' : X' ⟶ M'.toGroupoids) (g : M' ⟶ M)
      (α : h ≫ f ≅ f' ≫ AlgebraicSpace.toGroupoids.map g),
      IsUniformCategoricalModuliSpace f' ∧ AlgebraicSpace.Etale g ∧
        AlgebraicSpace.Separated g ∧
          (PseudoPullbackCone.mk f (AlgebraicSpace.toGroupoids.map g)
            X' h f' α).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack
