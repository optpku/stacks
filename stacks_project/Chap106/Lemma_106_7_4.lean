module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.InfinitesimalLifts
import StacksCheckRecall

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

/- Lemma 106.7.4. Let `X` be an algebraic stack over a scheme `S` whose
structure morphism `X ⟶ S` is locally of finite presentation. Let
`(A' ⟶ A, x)` be a deformation situation. If there exists a faithfully
flat finitely presented `A'`-algebra `B'` and an object `y'` of `X` over
`B'` lifting `x` restricted to `B' ⊗[A'] A`, then there exists an object
over `A'` lifting `x`. -/
@[stacks 0DNU] #check
  (AlgebraicGeometry.GroupoidsOver.exists_lift_of_faithfullyFlat_finitePresentation :
    ∀
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFinitePresentation
      (baseProjection.{u + 1, u, u + 1} X)]
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA))
    {B' : CommRingCat.{u}} (g : A' ⟶ B') (hg_ff : g.hom.FaithfullyFlat)
    (hg_fp : g.hom.FinitePresentation)
    (y' : infinitesimalLiftCat fA hfA x (Scheme.AffineOver.spec g)),
    Nonempty (liftCat x fA hfA))
