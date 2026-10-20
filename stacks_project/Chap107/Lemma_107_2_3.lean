module

public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Lemma_98_8_1
public import stacks_project.Chap100.Lemma_100_4_1_FieldValuedPoint
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap107.Situation_107_2_1_Instances
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Deformation
import StacksCheckRecall

/-!
# Deformation categories at finite-type field-valued points

In Situation 107.2.1, the predeformation functor `ℱ_{X, k, x0}` attached to a
finite-type field-valued point is a deformation category, and both its tangent
space and its infinitesimal automorphism space are finite-dimensional over `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor ArtinianLocalAlgCat
open FiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor

noncomputable section

universe u

section Evaluation

variable {S : Scheme.{u}} {X : GroupoidsOver S}
    (x0 : AlgebraicStack.FieldValuedPoint X)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.fiberObj_over x0 :
  X.p.obj ((toFunctor x0.hom).obj (Over.mk (𝟙 (Over.mk x0.structureHom)))) =
    Over.mk x0.structureHom)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.fiberObj x0 :
  X.p.Fiber (Over.mk x0.structureHom))

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.fiberObj_spec x0 :
  Fiber.fiberInclusion.obj x0.fiberObj =
      (toFunctor x0.hom).obj (Over.mk (𝟙 (Over.mk x0.structureHom))) ∧
    X.p.obj ((toFunctor x0.hom).obj (Over.mk (𝟙 (Over.mk x0.structureHom)))) =
      Over.mk x0.structureHom)

end Evaluation

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
    [Module.Finite Λ x0.K] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
        x0.structureHom)

/- Lemma 107.2.3. The predeformation category at a finite-type field-valued point
of an algebraic stack locally of finite type over a locally Noetherian scheme
is a deformation category, with finite-dimensional tangent and infinitesimal
automorphism spaces. -/
@[stacks 0DQW]
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.instIsDeformationCategory_predeformationFunctor
  X openImmersion x0.structureHom h_factor x0.fiberObj :
  Functor.IsDeformationCategory
    (predeformationFunctor X openImmersion x0.structureHom h_factor x0.fiberObj))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.instFiniteDimensional_tangentSpace
  openImmersion x0.structureHom h_factor X x0.fiberObj :
  FiniteDimensional x0.K
    ((Functor.fiberIsoClassFunctor
        (predeformationFunctor X openImmersion x0.structureHom h_factor
          x0.fiberObj)).obj
      (dualNumber Λ x0.K)))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.instFiniteDimensional_infinitesimalAutomorphisms
  openImmersion x0.structureHom h_factor X x0.fiberObj :
  FiniteDimensional x0.K
    (Functor.infinitesimalAutomorphisms
      (predeformationFunctor X openImmersion x0.structureHom h_factor
        x0.fiberObj)))

end AlgebraicGeometry.GroupoidsOver.Predeformation
