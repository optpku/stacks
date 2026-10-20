/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import ReasLib.RepresentationTheory.Homological.ContCohomology.DiscreteCochains
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.Topology.Algebra.Group.Basic
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Cohomology
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Injective
public import ReasLib.RingTheory.Finiteness.Projective

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Action
open CategoryTheory.Action.ModuleCat
open scoped MonoidalCategory

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

/-- The explicit contragredient diagonal tensor representation of two discrete modules. -/
noncomputable def dualTensorRep
    {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M N : DiscreteModuleCat R G) : Rep R G :=
  Rep.of
    (((Rep.ActionToRep R G).obj M.obj).ρ.dual.tprod
      ((Rep.ActionToRep R G).obj N.obj).ρ)

/-- The carrier of `dualTensorRep` is the dual-tensor module. -/
theorem dualTensorRep_V
    {R G : Type u} [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (M N : DiscreteModuleCat R G) :
    (dualTensorRep M N).V =
      TensorProduct R (Module.Dual R ((Rep.ActionToRep R G).obj M.obj).V)
        ((Rep.ActionToRep R G).obj N.obj).V := sorry

/-- The contragredient diagonal tensor action on a discrete module category. -/
theorem dualTensor_openStabilizer
    {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M N : DiscreteModuleCat R G)
    (hM : Module.FiniteProjective R M.obj.V) :
    openStabilizer R G
      ((Rep.RepToAction R G).obj (dualTensorRep M N)) := sorry

/-- The explicit discrete-continuous action underlying `Mᵛ ⊗ N`. -/
noncomputable def dualTensor
    {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M N : DiscreteModuleCat R G)
    (hM : Module.FiniteProjective R M.obj.V) : DiscreteModuleCat R G :=
  { obj :=
      (Rep.RepToAction R G).obj (dualTensorRep M N)
    property := dualTensor_openStabilizer M N hM }

/-- The underlying action of `dualTensor` is the contragredient tensor action. -/
theorem dualTensor_obj
    {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M N : DiscreteModuleCat R G)
    (hM : Module.FiniteProjective R M.obj.V) :
    (dualTensor M N hM).obj =
      (Rep.RepToAction R G).obj (dualTensorRep M N) := sorry

/-- For a finite projective discrete module, Ext is represented by derived-invariants cohomology with dual-tensor coefficients. -/
theorem ext_groupCohomology_iso_of_finiteProjective
    {R G : Type u} [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (M N : DiscreteModuleCat R G) (i : ℕ)
    (hM : Module.FiniteProjective R M.obj.V) :
    Nonempty
      (ModuleCat.of R (CategoryTheory.Abelian.Ext M N i) ≅
        cohomologyObject R G i (dualTensor M N hM)) := sorry

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
