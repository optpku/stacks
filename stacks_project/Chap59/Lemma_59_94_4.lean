/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_94_3
public import stacks_project.Chap59.Lemma_59_93_3
public import stacks_project.Chap59.Proposition_59_93_2
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

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] (sbar : GeometricPoint S)
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

/-- Lemma 59.94.4: if `f : X ⟶ S` is smooth and proper and `F` is a locally
constant abelian étale sheaf on `X` whose geometric stalks are torsion of order
prime to the residue characteristic, then for every geometric point `sbar` of
`S` and every geometric point `tbar` of `Spec(O^sh_{S, sbar})` the
specialization map
`derivedPushforwardSpecialization : (Rf_* F)_sbar ⟶ (Rf_* F)_tbar` is an
isomorphism. -/
@[stacks 0GKD]
theorem isIso_derivedPushforwardSpecialization_of_locallyConstant
    (F : Coefficients X) [Sheaf.IsLocallyConstant F]
    (hF : geometricStalk_isPrimeToCharTorsion F) :
    IsIso (derivedPushforwardSpecialization f sbar Rsh tbar (etaleSheafInDegreeZero F)) :=
  sorry

end AlgebraicGeometry.Scheme
