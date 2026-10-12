/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Definition 59.95.1: for a quasi-compact and quasi-separated scheme `X`,
the cohomological dimension is the least `n : WithTop ℕ` such that every
locally torsion abelian sheaf on its small étale site has vanishing cohomology
in degrees strictly above `n`. The cohomological dimension of a commutative
ring `A` means the dimension of `Spec (CommRingCat.of A)`. -/
@[stacks 0F0Q] #check (AlgebraicGeometry.Scheme.cohomologicalDimension :
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})], WithTop ℕ)

end
