/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Field
public import ReasLib.FieldTheory.Galois.Cohomology.BrauerVanishing
public import ReasLib.Algebra.CentralSimple.BrauerGroup.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Action.ModuleCat

universe u

noncomputable section

namespace GaloisCohomology

/-- For a transcendence-degree-one extension of an algebraically closed field, continuous
Galois cohomology of separable-closure units vanishes in every positive degree. -/
theorem unitsCohomology_isZero_of_trdeg_one
    {k : Type u} [Field k] [IsAlgClosed k] (K Ksep : Type u)
    [Field K] [Field Ksep] [Algebra k K] [Algebra K Ksep] [IsSepClosure K Ksep]
    (htr : Algebra.trdeg k K = 1) (q : ℕ) (hq : 1 ≤ q) :
    IsZero (DiscreteModuleCat.continuousCohomology
      (Gal(Ksep/K)) (unitsModule K Ksep) q) := sorry

end GaloisCohomology

namespace AlgebraicGeometry.Scheme.Etale.Small

/-- For a transcendence-degree-one extension of an algebraically closed field, small étale
cohomology of its spectrum with coefficients in the multiplicative-group sheaf vanishes in
every positive degree. -/
theorem etaleUnitsCohomology_isZero_of_trdeg_one
    {k : Type u} [Field k] [IsAlgClosed k] (K : Type u) [Field K] [Algebra k K]
    (htr : Algebra.trdeg k K = 1)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology q).obj
      (unitsAddSheaf (Spec (.of K)))) := sorry

end AlgebraicGeometry.Scheme.Etale.Small

end
