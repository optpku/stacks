/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact products of abelian groups at arbitrary index sizes

Mathlib's `AddCommGrpCat` product exactness instance is presented at the coefficient universe.
This leaf exposes the universe-polymorphic form needed by indexed Cech and product resolutions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w z

namespace CategoryTheory

variable [HasProducts.{w} AddCommGrpCat.{z}]

/-- Products of any declared size in `AddCommGrpCat` are exact. -/
@[stacks 079B "universe-polymorphic exact products of abelian groups"]
noncomputable instance addCommGrpCat_ab4StarOfSize :
    AB4StarOfSize.{w} AddCommGrpCat.{z} := sorry

end CategoryTheory
