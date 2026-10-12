/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Theorem_59_68_5_EtaleUnits
public import stacks_project.Chap59.Theorem_59_61_6_Cohomology
public import stacks_project.Chap59.Definition_59_57_2
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Etale.Small
  CategoryTheory CategoryTheory.Limits
open CategoryTheory.Action.ModuleCat

universe u

noncomputable section

namespace GaloisCohomology

/-- Lemma 59.67.12: if `k` is algebraically closed and `K / k` is a field extension of
transcendence degree 1, then small-etale cohomology of `unitsAddSheaf` on `Spec (.of K)`
vanishes in every degree `q ≥ 1`. -/
@[stacks 03RG]
theorem etaleUnitsCohomologyIsZeroOfTrdegOne
    {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    (htrdeg : Algebra.trdeg k K = 1)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology q).obj
      (unitsAddSheaf (Spec (.of K)))) := sorry

/-- If `k` is algebraically closed and `K / k` has transcendence degree 1, then continuous
Galois cohomology of `unitsModule K Ksep` vanishes in every degree `q ≥ 1`. -/
theorem unitsCohomologyIsZeroOfTrdegOne
    {k K Ksep : Type u} [Field k] [IsAlgClosed k] [Field K] [Field Ksep]
    [Algebra k K] [Algebra K Ksep] [IsSepClosure K Ksep]
    (htrdeg : Algebra.trdeg k K = 1) (q : ℕ) (hq : 1 ≤ q) :
    IsZero (DiscreteModuleCat.continuousCohomology (Gal(Ksep/K))
      (unitsModule K Ksep) q) := sorry

end GaloisCohomology
