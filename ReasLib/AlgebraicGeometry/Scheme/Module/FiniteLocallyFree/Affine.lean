/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.RingTheory.Flatness.LocallyFree

/-!
# Affine criteria for finite local freeness of scheme modules

This leaf compares the standard module properties of an `R`-module with the corresponding
properties of its associated quasi-coherent module on `Spec R`.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver TopCat.addCommGrpWEqualsLocallyBijectiveSelf
  TopCat.addCommGrpWEqualsLocallyBijective in
/-- A finite global generating family of an associated sheaf gives finite generation of
the original module. The epimorphism is reflected through the native tilde functor. -/
theorem module_finite_of_tilde_generatingSections
    {R : CommRingCat.{u}} (M : ModuleCat R)
    (G : (tilde M).GeneratingSections) [G.IsFiniteType] : Module.Finite R M := by
  classical
  let p : ModuleCat.of R (G.I →₀ R) ⟶ M :=
    (tilde.functor R).preimage ((tildeFinsupp G.I).hom ≫ G.π)
  have hp : (tilde.functor R).map p = (tildeFinsupp G.I).hom ≫ G.π :=
    (tilde.functor R).map_preimage _
  haveI : Epi G.π := G.epi
  haveI : Epi (tildeFinsupp (R := R) G.I).hom := by infer_instance
  haveI : Epi ((tilde.functor R).map p) := by
    rw [hp, epi_comp_iff_of_epi]
    exact G.epi
  haveI : Epi p := (tilde.functor R).epi_of_epi_map inferInstance
  exact Module.Finite.of_surjective p.hom ((ModuleCat.epi_iff_surjective p).mp inferInstance)

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- Finite module generators give a finite local generating family for the associated sheaf.
The relations may be arbitrary; only the generator index is used for finite type. -/
theorem tilde_isFiniteType_of_module_finite
    {R : CommRingCat.{u}} (M : ModuleCat R) [h : Module.Finite R M] :
    SheafOfModules.IsFiniteType (tilde M) := by
  classical
  letI : ∀ U : (Spec R).Opens,
      HasWeakSheafify ((Opens.grothendieckTopology (Spec R)).over U)
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  letI : ∀ U : (Spec R).Opens,
      ((Opens.grothendieckTopology (Spec R)).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  obtain ⟨s, hs⟩ := h
  let P := presentationTilde M (s : Set M) hs
    (LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M))) (Submodule.span_eq _)
  refine ⟨P.generators.localGeneratorsData, ⟨fun U ↦ ⟨?_⟩⟩⟩
  change Finite s
  infer_instance

/-- The associated module sheaf `M^~` on `Spec R` is of finite type exactly when
the `R`-module `M` is finite. -/
@[stacks 01PB]
theorem tilde_isFiniteType_iff_module_finite
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsFiniteType (tilde M) ↔ Module.Finite R M := sorry

/-- The associated module sheaf `M^~` on `Spec R` is of finite presentation
exactly when the `R`-module `M` is finitely presented. -/
@[stacks 01PC]
theorem tilde_isFinitePresentation_iff_module_finitePresentation
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsFinitePresentation (tilde M) ↔ Module.FinitePresentation R M := sorry

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- The associated module sheaf of a finitely presented module is finitely presented. -/
instance instIsFinitePresentationTilde
    {R : CommRingCat.{u}} (M : ModuleCat R) [Module.FinitePresentation R M] :
    SheafOfModules.IsFinitePresentation (tilde M) := by
  classical
  letI : ∀ U : (Spec R).Opens,
      HasWeakSheafify ((Opens.grothendieckTopology (Spec R)).over U)
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  letI : ∀ U : (Spec R).Opens,
      ((Opens.grothendieckTopology (Spec R)).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  obtain ⟨s, hs, t, ht⟩ := Module.FinitePresentation.out (R := R) (M := M)
  let P := presentationTilde M (s : Set M) hs (t : Set (s →₀ R)) ht
  refine ⟨P.quasicoherentData, ⟨fun U ↦ ⟨⟨?_⟩, ⟨?_⟩⟩⟩⟩
  · change Finite s
    infer_instance
  · change Finite t
    infer_instance

/-- The associated module sheaf `M^~` on `Spec R` is flat exactly when the
`R`-module `M` is flat. -/
@[stacks 05P0]
theorem tilde_isFlat_iff_module_flat
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsFlat (X := (Spec R).toRingedSpace) (tilde M) ↔
      Module.Flat R M := sorry

/-- The associated module sheaf `M^~` on `Spec R` is locally free exactly
when the `R`-module `M` is locally free. -/
@[stacks 05JM]
theorem tilde_isLocallyFree_iff_module_locallyFree
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsLocallyFree
      (J := Opens.grothendieckTopology (Spec R).toRingedSpace)
      (R := (Spec R).toRingedSpace.ringCatSheaf) (tilde M) ↔
      Module.LocallyFree R M := sorry

/-- The associated module sheaf `M^~` on `Spec R` is finite locally free
exactly when the `R`-module `M` is finite locally free. -/
@[stacks 05JM]
theorem tilde_isFiniteLocallyFree_iff_module_finiteLocallyFree
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsFiniteLocallyFree (tilde M) ↔
      Module.FiniteLocallyFree R M := sorry

end AlgebraicGeometry.Scheme.Modules
