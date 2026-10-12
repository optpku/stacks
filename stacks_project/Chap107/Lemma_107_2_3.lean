/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Lemma_98_8_1
public import stacks_project.Chap100.Lemma_100_4_1_FieldValuedPoint
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap107.Situation_107_2_1_Instances
import Mathlib.Tactic.CrossRefAttribute

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

namespace AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Evaluating the 1-morphism of a field-valued point on the identity slice
object lies over `Spec(k) ⟶ S`. -/
theorem fiberObj_over (x0 : FieldValuedPoint X) :
    X.p.obj ((toFunctor x0.hom).obj (GroupoidsOver.sliceIdentityObject x0.structureHom)) =
      Over.mk x0.structureHom :=
  sorry

/-- The object of `X` over `Spec(k) ⟶ S` obtained by evaluating the 1-morphism of
a field-valued point on the identity slice object. -/
def fiberObj (x0 : FieldValuedPoint X) :
    X.p.Fiber (Over.mk x0.structureHom) :=
  Fiber.mk (fiberObj_over x0)

/-- The fibre object of a field-valued point is the evaluation of its 1-morphism
on the identity slice object, and that object lies over `Spec(k) ⟶ S`. -/
theorem fiberObj_spec (x0 : FieldValuedPoint X) :
    Fiber.fiberInclusion.obj x0.fiberObj =
        (toFunctor x0.hom).obj (GroupoidsOver.sliceIdentityObject x0.structureHom) ∧
      X.p.obj ((toFunctor x0.hom).obj
          (GroupoidsOver.sliceIdentityObject x0.structureHom)) =
        Over.mk x0.structureHom :=
  sorry

end AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

open AlgebraicGeometry.AlgebraicStack (FieldValuedPoint)

/-- Lemma 107.2.3 (1): In Situation 107.2.1, if `x0 : Spec(k) ⟶ X` is a morphism
with `k` of finite type over `S`, then the predeformation functor
`p : ℱ_{X, k, x0} ⥤ ArtinianLocalAlgCat Λ k` is a deformation category. -/
@[stacks 0DQW]
instance instIsDeformationCategory_fieldValuedPoint {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
    [Module.Finite Λ x0.K] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
        x0.structureHom) :
    Functor.IsDeformationCategory
      (predeformationFunctor X openImmersion x0.structureHom h_factor x0.fiberObj) :=
  sorry

/-- Lemma 107.2.3 (2): In Situation 107.2.1, if `x0 : Spec(k) ⟶ X` is a morphism
with `k` of finite type over `S`, then the tangent space
`T ℱ_{X, k, x0}` is a finite-dimensional `k`-vector space. -/
@[stacks 0DQW]
instance instFiniteDimensional_tangentSpace {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
    [Module.Finite Λ x0.K] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
        x0.structureHom) :
    FiniteDimensional x0.K
      ((Functor.fiberIsoClassFunctor
          (predeformationFunctor X openImmersion x0.structureHom h_factor
            x0.fiberObj)).obj
        (dualNumber Λ x0.K)) :=
  sorry

/-- Lemma 107.2.3 (3): In Situation 107.2.1, if `x0 : Spec(k) ⟶ X` is a morphism
with `k` of finite type over `S`, then `Inf(ℱ_{X, k, x0})` is a
finite-dimensional `k`-vector space. -/
@[stacks 0DQW]
instance instFiniteDimensional_infinitesimalAutomorphisms {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
    [Module.Finite Λ x0.K] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
        x0.structureHom) :
    FiniteDimensional x0.K
      (Functor.infinitesimalAutomorphisms
        (predeformationFunctor X openImmersion x0.structureHom h_factor
          x0.fiberObj)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
