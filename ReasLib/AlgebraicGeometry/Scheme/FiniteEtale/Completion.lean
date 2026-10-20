/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.FiniteLocallyFree

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Full faithfulness of completion on finite locally free coherent modules implies
full faithfulness of restriction on finite étale schemes. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_completion
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (h_completion : Nonempty (CoherentCompletion.onFiniteLocallyFree I).FullyFaithful) :
    Nonempty (finiteEtaleBaseChange I.subschemeι).FullyFaithful := sorry

/-- Completeness of every finite locally free coherent module implies full faithfulness of
restriction on finite étale schemes. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_finiteLocallyFree_sections
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (h_complete : ∀ E : RingedSpace.Coh X.toRingedSpace,
      CoherentCompletion.finiteLocallyFree X E →
        Function.Bijective (CoherentCompletion.sectionsComparison I E.obj)) :
    Nonempty (finiteEtaleBaseChange I.subschemeι).FullyFaithful := sorry

/-- Eventual completeness of tensor powers of an ample invertible module implies full
faithfulness of restriction on finite étale schemes. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_ample_sections
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (L : X.Modules)
    (hL : Modules.isAmpleObject L)
    (h_complete : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Function.Bijective
        (CoherentCompletion.sectionsComparison I (RingedSpace.TensorPower.sheaf L m))) :
    Nonempty (finiteEtaleBaseChange I.subschemeι).FullyFaithful := sorry

/-- Quasi-affineness and completeness of the structure module imply full faithfulness of
restriction on finite étale schemes. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_quasiAffine_sections
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (hX : X.IsQuasiAffine)
    (h_complete : Function.Bijective
      (CoherentCompletion.sectionsComparison I (SheafOfModules.unit X.ringCatSheaf))) :
    Nonempty (finiteEtaleBaseChange I.subschemeι).FullyFaithful := sorry

/-- If completion is an equivalence on finite locally free coherent modules, then
restriction along the closed subscheme is an equivalence on finite étale schemes. -/
instance finiteEtaleBaseChange_isEquivalence_of_completion
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    [Functor.IsEquivalence (CoherentCompletion.onFiniteLocallyFreeToFiniteLocallyFree I)] :
    Functor.IsEquivalence (finiteEtaleBaseChange I.subschemeι) := sorry

end AlgebraicGeometry.Scheme
