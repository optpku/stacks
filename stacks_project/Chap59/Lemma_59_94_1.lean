module

public import stacks_project.Chap59.Lemma_59_94_1_Cospecialization
public import stacks_project.Chap59.Definition_59_93_1_LocalAcyclicity
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.EtaleVanishingCycles
open DerivedCategory.TStructure

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S) (sbar : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk sbar.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar Rsh))
variable (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh)
variable (hiS : iS ≫ strictHenselizationMap S sbar Rsh = sbar.hom)
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

/-- Lemma 59.94.1: in the §59.94 setup, if `K` is bounded below and `f` is locally
acyclic relative to `K`, then `i⁻¹ β_{K,sbar,tbar}` is an isomorphism in
`D((X_sbar)_etale)`. -/
@[stacks 0GJU]
theorem isIso_inverseImage_etaleCohomologyBeta (K : Complexes X)
    (hK : t.plus K) [LocallyAcyclicRelative f K] :
    IsIso ((derivedInverseImage (cospecializationI f sbar Rsh iS hiS)).map
      (etaleCohomologyBeta f sbar Rsh tbar K)) := sorry

end AlgebraicGeometry.Scheme
