/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_67_2_ProP
public import stacks_project.Chap59.Lemma_59_67_1_Torsion
public import stacks_project.Chap59.Theorem_59_51_3_Cohomology
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 59.67.2: for a prime `ℓ` and `n > 0`, a field `K` with separable
closure `Ksep`, `G = Gal(Ksep/K)`, and a maximal pro-`ℓ` subgroup `H ⊆ G`
with corresponding extension `L = IntermediateField.fixedField H`, vanishing of
`H^n_étale(Spec K, F)` for every locally `ℓ`-power torsion abelian étale sheaf
`F` is equivalent to vanishing of `H^n_étale(Spec L, constant ZMod ℓ)`. -/
@[stacks 0DV8]
theorem etaleCohomology_ellPowerTorsion_vanishes_iff_constantZMod
    {ℓ n : ℕ} [Fact (Nat.Prime ℓ)] (hn : 0 < n)
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (H : Subgroup Gal(Ksep/K)) (hH : IsMaximalProPSubgroup ℓ H)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify (Spec (.of (IntermediateField.fixedField H))).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasWeakSheafify (Spec (.of (IntermediateField.fixedField H))).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasExt.{u}
      (Sheaf (Spec (.of (IntermediateField.fixedField H))).smallEtaleTopology
        AddCommGrpCat.{u})] :
    (∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u},
        IsLocallyEllPowerTorsion ℓ F →
          IsZero (F.H' n (globalEtale (Spec (.of K))))) ↔
      IsZero
        (((constantSheaf (Spec (.of (IntermediateField.fixedField H))).smallEtaleTopology
              AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))).H' n
          (globalEtale (Spec (.of (IntermediateField.fixedField H))))) := sorry

end AlgebraicGeometry.Scheme.Etale

end
