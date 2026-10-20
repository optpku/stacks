module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap59.Proposition_59_55_2_Over

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Coproduct

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint

universe u

/- The fibrewise coproduct of abelian étale stalks. -/
#check (AlgebraicGeometry.Scheme.Etale.abelianStalkCoproduct :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y),
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u})
