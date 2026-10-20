module

public import ReasLib.GroupTheory.ProP
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion.Primary
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- For a prime `ℓ` and positive degree `n`, étale cohomology over a field `K`
vanishes for every locally `ℓ`-power torsion abelian sheaf if and only if
degree-`n` cohomology with constant `ZMod ℓ` coefficients vanishes over the
fixed field of a maximal pro-`ℓ` subgroup of its absolute Galois group. -/
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
        CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ F →
          IsZero (F.H' n (globalEtale (Spec (.of K))))) ↔
      IsZero
        (((constantSheaf (Spec (.of (IntermediateField.fixedField H))).smallEtaleTopology
              AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))).H' n
          (globalEtale (Spec (.of (IntermediateField.fixedField H))))) := sorry

/-- For a prime `ℓ` and positive degree `n`, étale cohomology over a field `K`
vanishes in every degree at least `n` for every locally `ℓ`-power torsion
abelian sheaf if and only if degree-`n` cohomology with constant `ZMod ℓ`
coefficients vanishes over the fixed field of a maximal pro-`ℓ` subgroup
of its absolute Galois group. -/
theorem etaleCohomology_ellPowerTorsion_vanishesFrom_iff_constantZMod
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
        CategoryTheory.Sheaf.IsLocallyPPowerTorsion ℓ F →
          ∀ q, n ≤ q → IsZero (F.H' q (globalEtale (Spec (.of K))))) ↔
      IsZero
        (((constantSheaf (Spec (.of (IntermediateField.fixedField H))).smallEtaleTopology
              AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))).H' n
          (globalEtale (Spec (.of (IntermediateField.fixedField H))))) := sorry

end AlgebraicGeometry.Scheme.Etale

end
