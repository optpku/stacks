/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_35_3_StructureSheaf

/-!
# Vanishing of higher étale cohomology of the structure sheaf

On a countably indexed affine formal algebraic space, positive-degree cohomology
of a structure sheaf on the small étale site vanishes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- Lemma 87.35.3: if `X` is a countably indexed affine formal algebraic space,
then `H^n(X_étale, 𝒪_X) = 0` for every `n > 0`. Here `𝒪_X` is a sheaf of rings
on the small étale site whose value on each `U_red` is the inverse-limit ring of
stage global sections of a directed affine thickening presentation of `U`. -/
@[stacks 0DEL]
theorem isZero_cohomology_structureSheaf (X : (Over S)ᵒᵖ ⥤ Type u)
    [AffineFormalAlgebraicSpace.IsCountablyIndexedAffine X] [Reduction X]
    (𝒪 : Sheaf (smallEtaleTopology X) RingCat.{u})
    [IsStructureSheaf 𝒪] (n : ℕ) (hn : 0 < n)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})] :
    IsZero
      ((Sheaf.functorH (smallEtaleTopology X) n).obj
        ((sheafCompose (smallEtaleTopology X)
            (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj 𝒪)) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
