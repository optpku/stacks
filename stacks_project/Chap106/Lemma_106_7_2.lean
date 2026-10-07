module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps
public import ReasLib.RingTheory.RingHom.SquareZero
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap106.Lemma_106_7_2_Presheaf

/-!
# Sheaf of infinitesimal lifts

On an algebraic stack whose inertia morphism is locally of finite presentation,
isomorphism classes of infinitesimal lifts of a square-zero deformation form a
sheaf on the big affine fppf site of the thickened base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 106.7.2. Let `X` be an algebraic stack over a base scheme `S`. Assume
`I_X ⟶ X` is locally of finite presentation. Let `(A' ⟶ A, x)` be a deformation
situation. Then the functor sending an affine scheme over `Spec A'` to the
isomorphism classes of lifts of `x` restricted to the thickening
`U ×_{Spec A'} Spec A` is a sheaf on `(Aff / Spec A')_fppf` of Topologies,
Definition 34.7.8. -/
@[stacks 0DNS]
theorem infinitesimalLiftPresheaf_isSheaf {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [Groupoids.Hom.LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X)]
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA)) :
    Presheaf.IsSheaf (Scheme.bigAffineFppfTopology (Spec A'))
      (infinitesimalLiftPresheaf fA hfA x) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
