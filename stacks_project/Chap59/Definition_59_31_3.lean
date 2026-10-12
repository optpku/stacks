/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 59.31.3 (1): the support of an abelian sheaf is the set of scheme
points with nonzero geometric stalk. -/
@[stacks 04FS] #check
  (AlgebraicGeometry.Scheme.Etale.abelianSheafSupport :
    ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}), Set S)

/- Definition 59.31.3 (2): the support of a section is the closed complement of
its largest vanishing open. -/
@[stacks 04FS] #check
  (AlgebraicGeometry.Scheme.Etale.abelianSheafSectionSupport :
    ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (U : S.Etale) (σ : F.1.obj (Opposite.op U)), TopologicalSpace.Closeds U.left)
