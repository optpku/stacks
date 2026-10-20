module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Lifts
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalLifts.Presheaf
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Local-to-global infinitesimal lifts along fppf algebras

On an algebraic stack locally of finite presentation over its base scheme,
a square-zero deformation has a lift whenever it has one over a faithfully
flat finitely presented algebra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- For an algebraic stack locally of finite presentation over its base scheme,
a fibre object over a square-zero quotient admits a lift if its restriction
admits a lift over a faithfully flat finitely presented algebra of the thickened
ring. -/
theorem exists_lift_of_faithfullyFlat_finitePresentation
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation
      (baseProjection.{u + 1, u, u + 1} X)]
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA))
    {B' : CommRingCat.{u}} (g : A' ⟶ B') (hg_ff : g.hom.FaithfullyFlat)
    (hg_fp : g.hom.FinitePresentation)
    (y' : infinitesimalLiftCat fA hfA x (Scheme.AffineOver.spec g)) :
    Nonempty (liftCat x fA hfA) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
