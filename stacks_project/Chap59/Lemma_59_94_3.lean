/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_94_2
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.EtaleVanishingCycles
open DerivedCategory.TStructure

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (sbar : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk sbar.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar Rsh))
variable
    [((smallEtalePullback (cospecializationH f sbar Rsh tbar)).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (henselizedFiber f sbar Rsh).smallEtaleTopology
        (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh))
          tbar.hom).smallEtaleTopology).IsRightAdjoint]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (directImage (cospecializationH f sbar Rsh tbar)))
      (HomologicalComplex.quasiIso
        (Coefficients
          (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom))
        (ComplexShape.up ℤ))]

/-- Lemma 59.94.3 (1): if `f : X ⟶ S` is proper and locally acyclic relative to a
bounded-below `K ∈ D⁺(X_étale)` with torsion cohomology sheaves, then for every
geometric point `sbar` of `S` and every geometric point `tbar` of
`Spec(O^sh_{S, sbar})` the specialization map
`sp = derivedPushforwardSpecialization : (Rf_* K)_sbar ⟶ (Rf_* K)_tbar` is an
isomorphism. -/
@[stacks 0GJW]
theorem isIso_derivedPushforwardSpecialization (K : Complexes X)
    (hK : t.plus K) [LocallyAcyclicRelative f K]
    (hTorsion : DerivedCategory.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Coefficients X)) K) :
    IsIso (derivedPushforwardSpecialization f sbar Rsh tbar K) := sorry

/-- Lemma 59.94.3 (2): if `f : X ⟶ S` is proper and locally acyclic relative to a
bounded-below `K ∈ D⁺(X_étale)` with torsion cohomology sheaves, then for every
geometric point `sbar` of `S` and every geometric point `tbar` of
`Spec(O^sh_{S, sbar})` the cospecialization map
`cosp = cospecializationMap : RΓ(X_tbar, K) ⟶ RΓ(X_sbar, K)` is an isomorphism. -/
@[stacks 0GJW]
theorem isIso_cospecializationMap
    (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh)
    (hiS : iS ≫ strictHenselizationMap S sbar Rsh = sbar.hom)
    (K : Complexes X) (hK : t.plus K) [LocallyAcyclicRelative f K]
    (hTorsion : DerivedCategory.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Coefficients X)) K) :
    IsIso (cospecializationMap f sbar Rsh tbar iS hiS K hK) := sorry

end AlgebraicGeometry.Scheme
