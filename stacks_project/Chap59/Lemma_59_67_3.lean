module

public import stacks_project.Chap59.Lemma_59_67_3_Torsion
public import stacks_project.Chap59.Lemma_59_67_2_ProP
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

/-- Lemma 59.67.3: for a prime `ℓ` and `n > 0`, a field `K` with separable
closure `Ksep`, `G = Gal(Ksep/K)`, and a maximal pro-`ℓ` subgroup `H ⊆ G`
with corresponding extension `L = IntermediateField.fixedField H`, vanishing of
`H^q_étale(Spec K, F)` for all `q ≥ n` and every locally `ℓ`-torsion abelian
étale sheaf `F` is equivalent to vanishing of
`H^n_étale(Spec L, constant ZMod ℓ)`. -/
@[stacks 0DV9]
theorem etaleCohomology_ellTorsion_vanishesFrom_iff_constantZMod
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
        IsLocallyEllTorsion ℓ F →
          ∀ q, n ≤ q → IsZero (F.H' q (globalEtale (Spec (.of K))))) ↔
      IsZero
        (((constantSheaf (Spec (.of (IntermediateField.fixedField H))).smallEtaleTopology
              AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))).H' n
          (globalEtale (Spec (.of (IntermediateField.fixedField H))))) := sorry

end AlgebraicGeometry.Scheme.Etale

end
