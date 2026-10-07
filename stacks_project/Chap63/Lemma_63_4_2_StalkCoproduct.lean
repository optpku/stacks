module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap59.Proposition_59_55_2_Over

/-!
# Coproduct of abelian étale stalks over a geometric point

The fibrewise coproduct `∐_{f(x̄)=ȳ} F_x̄` of abelian étale sheaf fibres, indexed
by same-field geometric points of `X` over `ȳ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

/-- The fibrewise coproduct of abelian étale stalks at geometric points of `X`
over `ybar`. -/
def abelianStalkCoproduct (ybar : GeometricPoint Y) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj G := ∐ fun x : Over f ybar ↦
    (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj G
  map {G H} φ := Limits.Sigma.map fun x : Over f ybar ↦
    (toSmallEtalePoint x.toGeometricPoint).sheafFiber.map φ
  map_id := sorry
  map_comp := sorry

/-- Evaluating the fibrewise abelian stalk coproduct recovers the coproduct of
sheaf fibres. -/
theorem abelianStalkCoproduct_obj (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproduct f ybar).obj F =
      ∐ fun x : Over f ybar ↦
        (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F :=
  rfl

/-- The coproduct functor acts on a morphism of abelian étale sheaves by the
coproduct of the induced stalk maps. -/
theorem abelianStalkCoproduct_map (ybar : GeometricPoint Y)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (abelianStalkCoproduct f ybar).map φ =
      Limits.Sigma.map fun x : Over f ybar ↦
        (toSmallEtalePoint x.toGeometricPoint).sheafFiber.map φ :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
