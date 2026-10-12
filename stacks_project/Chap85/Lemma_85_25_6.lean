/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import stacks_project.Chap85.Lemma_85_25_1_Forget
public import stacks_project.Chap85.Lemma_85_25_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_25_6_Cohomology

/-!
# Lemma 85.25.6

A first-quadrant spectral sequence with `E₁^{p,q} = H^q(U_p, F_p)` converging
to `H^{p+q}(X, F)`, for a proper hypercovering in `LCCat`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.SimplicialObject
open scoped Simplicial

noncomputable section

universe u v

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
variable [HasExt.{v} (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})]
variable [∀ n : ℕ, HasSheafify
    (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋n⦌))) AddCommGrpCat.{u}]
variable [∀ n : ℕ, HasExt.{v}
    (Sheaf (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋n⦌))) AddCommGrpCat.{u})]

/-- Lemma 85.25.6. Let `U` be a simplicial object of `LCCat` and let `a : U ⟶ X` be an
augmentation. Let `F` be an abelian sheaf on `X`. Let `F_n` be the pullback to `U_n`.
If `U` is a proper hypercovering of `X`, then there exists a canonical first-quadrant
spectral sequence with `E₁^{p,q} = H^q(U_p, F_p)` converging to `H^{p+q}(X, F)`. -/
@[stacks 09XB]
theorem exists_spectralSequence (ha : IsProperHypercovering a)
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          stageCohomology (toTopCatAugmentation a) F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (Opens.grothendieckTopology X.obj) n).obj F) :=
  sorry

end LCCat
