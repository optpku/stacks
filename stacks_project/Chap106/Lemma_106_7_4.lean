module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.RingTheory.RingHom.SquareZero
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap98.Lemma_98_21_1
public import stacks_project.Chap106.Lemma_106_7_2_Presheaf
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap107.Situation_107_2_1_Instances

/-!
# Local-to-global infinitesimal lifts along fppf algebras

On an algebraic stack whose structure morphism is locally of finite
presentation, a lift of a square-zero deformation over a faithfully flat
finitely presented algebra descends to a lift over the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The affine scheme over `Spec A` associated to an algebra map `g : A ⟶ B`. -/
def specAffineOver {A B : CommRingCat.{u}} (g : A ⟶ B) :
    (Spec A).AffineOver :=
  Scheme.AffineOver.mk (Spec B) inferInstance (Spec.map g)

/-- The structure morphism of `specAffineOver g` is `Spec.map g`. -/
theorem specAffineOver_hom {A B : CommRingCat.{u}} (g : A ⟶ B) :
    (Scheme.AffineOver.obj (specAffineOver g)).hom = Spec.map g :=
  sorry

/-- The category of objects over an affine test scheme `U` lifting the
restriction of `x` to the infinitesimal thickening `U ×_{Spec A'} Spec A`. -/
abbrev infinitesimalLiftCat {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) (U : (Spec A').AffineOver) :=
  UnderLift X.p (infinitesimalLiftThickeningOverHom σA σA' fA hfA U)
    (infinitesimalLiftRestrict σA fA x U)

/-- `infinitesimalLiftCat fA hfA x U` is the fibered lift category of the
restricted fibre object along the infinitesimal thickening of `U`. -/
theorem infinitesimalLiftCat_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) (U : (Spec A').AffineOver) :
    infinitesimalLiftCat fA hfA x U =
      UnderLift X.p (infinitesimalLiftThickeningOverHom σA σA' fA hfA U)
        (infinitesimalLiftRestrict σA fA x U) :=
  sorry

/-- Lemma 106.7.4. Let `X` be an algebraic stack over a scheme `S` whose
structure morphism `X ⟶ S` is locally of finite presentation. Let
`(A' ⟶ A, x)` be a deformation situation. If there exists a faithfully
flat finitely presented `A'`-algebra `B'` and an object `y'` of `X` over
`B'` lifting `x` restricted to `B' ⊗[A'] A`, then there exists an object
over `A'` lifting `x`. -/
@[stacks 0DNU]
theorem exists_lift_of_faithfullyFlat_finitePresentation
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation
      (baseProjection.{u + 1, u, u + 1} X)]
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA))
    {B' : CommRingCat.{u}} (g : A' ⟶ B') (hg_ff : g.hom.FaithfullyFlat)
    (hg_fp : g.hom.FinitePresentation)
    (y' : infinitesimalLiftCat fA hfA x (specAffineOver g)) :
    Nonempty (liftCat x fA hfA) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
