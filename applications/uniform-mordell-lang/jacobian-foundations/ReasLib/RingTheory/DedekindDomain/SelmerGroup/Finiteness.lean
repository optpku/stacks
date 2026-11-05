/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

Adapted from MichaelStollBayreuth/EllipticCurves at
4c43c4089d2960904c0a4c1bb4668e827d80a62d.
Source fragments: SelmerGroup.lean:90-92, SelmerGroup.lean:476-479, SelmerGroup.lean:700-700, SelmerGroup.lean:894-911, SelmerGroup.lean:1049-1049.
Changes: extracted arithmetic dependency layers, narrowed imports, and documented ownership.
The upstream files have no per-file copyright header; repository license and author retained.
-/
module

public import ReasLib.RingTheory.DedekindDomain.SelmerGroup.ExactSequence
public import ReasLib.RingTheory.DedekindDomain.SUnits
public import Mathlib.GroupTheory.Index

/-!
# Finiteness of the general arithmetic Selmer group

For any Dedekind domain with finitely generated units and finite class group,
finite `S` and nonzero natural `n` give a finite Mathlib Selmer group. The proof uses
the S-unit image and finite S-class group, at their stated hypotheses. No number field,
elliptic curve or geometric application is imported.
-/

@[expose] public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

variable (S : Set (HeightOneSpectrum R)) (n : ℕ)

variable (R) in
/-- **The Selmer group `K(S,n)` is finite**, provided that the class group of `R` is finite, that
`Rˣ` is finitely generated, that `S` is finite and that `n ≠ 0`.

The image of `sUnitModPowToSelmer` is finite, since its source is the quotient of a finitely
generated commutative group (`fg_sUnit`) by its `n`-th powers (`CommGroup.finite_modPow`).
By `ker_toSClassGroup` that image is the kernel of `toSClassGroup`, whose target
`ClassGroup (S.integer K)` is finite by `SInteger.finite_classGroup`. -/
theorem finite_selmerGroup [Finite (ClassGroup R)] [Group.FG Rˣ] (hS : S.Finite) [NeZero n] :
    Finite (selmerGroup (K := K) (S := S) (n := n)) := by
  have := fg_sUnit K S hS
  have hker : Finite (toSClassGroup K S n).ker := by
    rw [ker_toSClassGroup, ← range_sUnitModPowToSelmer]
    have := CommGroup.finite_modPow (G := S.unit K) n
    exact Finite.Set.finite_range _
  have hquot : Finite (selmerGroup (K := K) (S := S) (n := n) ⧸ (toSClassGroup K S n).ker) :=
    .of_injective _ (QuotientGroup.kerLift_injective (toSClassGroup K S n))
  exact Finite.of_subgroup_quotient (toSClassGroup K S n).ker

end IsDedekindDomain

end
