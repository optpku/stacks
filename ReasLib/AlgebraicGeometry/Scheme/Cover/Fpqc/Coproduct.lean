/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Criteria
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Over

/-!
# Fpqc coverings and coproducts

This module compares an indexed fpqc covering family with the singleton family formed from its
coproduct descent morphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {ι : Type v}

/-- An indexed family of scheme morphisms is an fpqc covering if and only if the singleton family
formed by its coproduct descent morphism is an fpqc covering. -/
theorem fpqcCovering_iff_coproductSingleton (X : ι → Over T)
    [HasCoproduct (fun i ↦ (X i).left)] :
    FpqcCovering X ↔
      FpqcCovering
        (FormalCoproduct.Over.coproductSingleton (FormalCoproduct.mk ι X)).obj := sorry

end AlgebraicGeometry.Scheme
