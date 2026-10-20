/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import ReasLib.CategoryTheory.Filtration.Biproduct
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import ReasLib.CategoryTheory.Filtration.Strict.Pullback
public import ReasLib.CategoryTheory.Filtration.Strict.Pushout
public import ReasLib.CategoryTheory.Filtration.KernelCokernel.Universal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preabelian Structure on Filtered Objects

Filtered objects in an abelian category form a preadditive category with zero object,
biproducts, kernels, and cokernels.  This module bundles the pairwise pullback and pushout
constructions as global instances, so standard Mathlib limit APIs work without local instance
reconstruction.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C]

/-- Filtered objects in an abelian category have all pullbacks. -/
@[stacks 0122]
noncomputable instance hasPullbacks [Abelian C] : HasPullbacks (FilteredObject C) :=
  hasPullbacks_of_hasLimit_cospan _

/-- The pullback structure on filtered objects in an abelian category. -/
noncomputable def pullbacks [Abelian C] : HasPullbacks (FilteredObject C) := hasPullbacks

/-- Filtered objects in an abelian category have all pushouts. -/
@[stacks 0122]
noncomputable instance hasPushouts [Abelian C] : HasPushouts (FilteredObject C) :=
  hasPushouts_of_hasColimit_span _

/-- The pushout structure on filtered objects in an abelian category. -/
noncomputable def pushouts [Abelian C] : HasPushouts (FilteredObject C) := hasPushouts

/-- Pullbacks and binary products provide all equalizers of filtered morphisms. -/
@[stacks 0122]
noncomputable instance hasEqualizers [Abelian C] : HasEqualizers (FilteredObject C) :=
  hasEqualizers_of_hasPullbacks_and_binary_products

/-- The equalizer structure on filtered objects in an abelian category. -/
noncomputable def equalizers [Abelian C] : HasEqualizers (FilteredObject C) := hasEqualizers

/-- A zero filtered object and pullbacks supply all finite limits of filtered objects. -/
@[stacks 0122]
noncomputable instance hasFiniteLimits [Abelian C] :
    HasFiniteLimits (FilteredObject C) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The finite-limit structure on filtered objects in an abelian category. -/
noncomputable def finiteLimits [Abelian C] : HasFiniteLimits (FilteredObject C) := hasFiniteLimits

/-- Pushouts and binary coproducts provide all coequalizers of filtered morphisms. -/
@[stacks 0122]
noncomputable instance hasCoequalizers [Abelian C] : HasCoequalizers (FilteredObject C) :=
  hasCoequalizers_of_hasPushouts_and_binary_coproducts

/-- The coequalizer structure on filtered objects in an abelian category. -/
noncomputable def coequalizers [Abelian C] : HasCoequalizers (FilteredObject C) := hasCoequalizers

/-- A zero filtered object and pushouts supply all finite colimits of filtered objects. -/
@[stacks 0122]
noncomputable instance hasFiniteColimits [Abelian C] :
    HasFiniteColimits (FilteredObject C) :=
  hasFiniteColimits_of_hasInitial_and_pushouts

/-- The finite-colimit structure on filtered objects in an abelian category. -/
noncomputable def finiteColimits [Abelian C] : HasFiniteColimits (FilteredObject C) := hasFiniteColimits

/-- Filtered objects in an abelian category have kernels. -/
@[stacks 0122]
noncomputable instance hasKernels [Abelian C] : HasKernels (FilteredObject C) where
  has_limit f := HasLimit.mk ⟨_, Hom.kernelιIsLimit f⟩

/-- The kernel structure on filtered objects in an abelian category. -/
noncomputable def kernels [Abelian C] : HasKernels (FilteredObject C) := hasKernels

/-- Filtered objects in an abelian category have cokernels. -/
@[stacks 0122]
noncomputable instance hasCokernels [Abelian C] : HasCokernels (FilteredObject C) where
  has_colimit f := HasColimit.mk ⟨_, Hom.toCokernelIsColimit f⟩

/-- The cokernel structure on filtered objects in an abelian category. -/
noncomputable def cokernels [Abelian C] : HasCokernels (FilteredObject C) := hasCokernels

end CategoryTheory.FilteredObject
