module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ProP
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.67.3: for a prime `ℓ` and `n > 0`, a field `K` with separable
closure `Ksep`, `G = Gal(Ksep/K)`, and a maximal pro-`ℓ` subgroup `H ⊆ G`
with corresponding extension `L = IntermediateField.fixedField H`, vanishing of
`H^q_étale(Spec K, F)` for all `q ≥ n` and every locally `ℓ`-power torsion abelian
étale sheaf `F` is equivalent to vanishing of
`H^n_étale(Spec L, constant ZMod ℓ)`. -/
@[stacks 0DV9]
#check (AlgebraicGeometry.Scheme.Etale.etaleCohomology_ellPowerTorsion_vanishesFrom_iff_constantZMod :
    ∀ {ℓ n : ℕ} [Fact (Nat.Prime ℓ)] (hn : 0 < n)
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
        AddCommGrpCat.{u})],
    (∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u},
        CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ F →
          ∀ q, n ≤ q → IsZero (F.H' q (globalEtale (Spec (.of K))))) ↔
      IsZero
        (((constantSheaf (Spec (.of (IntermediateField.fixedField H))).smallEtaleTopology
              AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))).H' n
          (globalEtale (Spec (.of (IntermediateField.fixedField H))))))

end AlgebraicGeometry.Scheme.Etale

end
