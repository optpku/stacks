/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- The constant-coefficient étale cohomology pullback has the expected scheme-theoretic type. -/
#check
  (AlgebraicGeometry.Scheme.Hom.etaleHq_constant_pullback :
    ∀ {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) (M : AddCommGrpCat.{u}) (q : ℕ),
      (Sheaf.functorH Z.smallEtaleTopology q).obj
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M) ⟶
        (Sheaf.functorH Z'.smallEtaleTopology q).obj
          ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M))

end AlgebraicGeometry.Scheme.Hom
