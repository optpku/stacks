/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisModule
public import ReasLib.FieldTheory.Galois.Cohomology.Coefficients
public import ReasLib.FieldTheory.Galois.Cohomology.Units
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Action ModuleCat
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.Small

universe u

noncomputable section

namespace GaloisCohomology

variable (K Ksep : Type u) [Field K] [Field Ksep]
  [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The geometric stalk of the constant `ZMod n` sheaf is the trivial discrete Galois module. -/
theorem constantZModEtaleStalk (n : ℕ)
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    IsIsomorphic
      (etaleStalk K Ksep
        ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod n)))))
      (constantZModModule K Ksep n) := sorry

/-- The geometric stalk of the units sheaf is the natural Galois module on separable-closure
units, written additively. -/
theorem unitsEtaleStalk :
    IsIsomorphic (etaleStalk K Ksep (unitsAddSheaf (Spec (.of K))))
      (unitsModule K Ksep) := sorry

/-- The geometric stalk of the additive structure sheaf is the additive Galois module on the
separable closure. -/
theorem additiveEtaleStalk :
    IsIsomorphic
      (etaleStalk K Ksep
        ((sheafCompose (Spec (.of K)).smallEtaleTopology
          (forget₂ RingCat AddCommGrpCat)).obj (structureSheaf (Spec (.of K)))))
      (additiveModule K Ksep) := sorry

/-- The geometric stalk of the kernel of multiplication by `n` on the additive units sheaf is
the Galois module on the `n`th roots of unity. -/
theorem rootsOfUnityEtaleStalk (n : ℕ) :
    IsIsomorphic
      (etaleStalk K Ksep (kernel (n • 𝟙 (unitsAddSheaf (Spec (.of K))))))
      (rootsOfUnityModule K Ksep n) := sorry

/-- Small étale cohomology of the units sheaf over a field agrees with derived-invariants
Galois cohomology of separable-closure units. -/
theorem etaleUnitsCohomologyIsomorphicGalois (i : ℕ)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology i).obj
        (unitsAddSheaf (Spec (.of K))))
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        ((DiscreteModuleCat.derivedCohomologyFunctor ℤ (Gal(Ksep / K)) i).obj
          (unitsModule K Ksep))) := sorry

/-- Small étale cohomology of the additive structure sheaf over a field agrees with
derived-invariants Galois cohomology of the additive separable closure. -/
theorem etaleAdditiveCohomologyIsomorphicGalois (i : ℕ)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology i).obj
        ((sheafCompose (Spec (.of K)).smallEtaleTopology
          (forget₂ RingCat AddCommGrpCat)).obj (structureSheaf (Spec (.of K)))))
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        ((DiscreteModuleCat.derivedCohomologyFunctor ℤ (Gal(Ksep / K)) i).obj
          (additiveModule K Ksep))) := sorry

/-- First small étale cohomology of the units sheaf over the spectrum of a field vanishes. -/
theorem etaleH1UnitsIsZero
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    IsZero ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology 1).obj
      (unitsAddSheaf (Spec (.of K)))) := sorry

/-- Positive-degree small étale cohomology of the additive structure sheaf over a field
vanishes. -/
theorem etaleAdditiveCohomologyIsZero (i : ℕ) (hi : 0 < i)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    IsZero ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology i).obj
      ((sheafCompose (Spec (.of K)).smallEtaleTopology
        (forget₂ RingCat AddCommGrpCat)).obj (structureSheaf (Spec (.of K))))) := sorry

end GaloisCohomology

end
