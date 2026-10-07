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
noncomputable instance hasPullbacks [Abelian C] : HasPullbacks (FilteredObject C) := sorry

/-- Filtered objects in an abelian category have all pushouts. -/
@[stacks 0122]
noncomputable instance hasPushouts [Abelian C] : HasPushouts (FilteredObject C) := sorry

/-- Pullbacks and binary products provide all equalizers of filtered morphisms. -/
@[stacks 0122]
noncomputable instance hasEqualizers [Abelian C] : HasEqualizers (FilteredObject C) :=
  hasEqualizers_of_hasPullbacks_and_binary_products

/-- A zero filtered object and pullbacks supply all finite limits of filtered objects. -/
@[stacks 0122]
noncomputable instance hasFiniteLimits [Abelian C] :
    HasFiniteLimits (FilteredObject C) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- Pushouts and binary coproducts provide all coequalizers of filtered morphisms. -/
@[stacks 0122]
noncomputable instance hasCoequalizers [Abelian C] : HasCoequalizers (FilteredObject C) :=
  hasCoequalizers_of_hasPushouts_and_binary_coproducts

/-- A zero filtered object and pushouts supply all finite colimits of filtered objects. -/
@[stacks 0122]
noncomputable instance hasFiniteColimits [Abelian C] :
    HasFiniteColimits (FilteredObject C) :=
  hasFiniteColimits_of_hasInitial_and_pushouts

/-- Filtered objects in an abelian category have kernels. -/
@[stacks 0122]
noncomputable instance hasKernels [Abelian C] : HasKernels (FilteredObject C) where
  has_limit f := HasLimit.mk ⟨_, Hom.kernelιIsLimit f⟩

/-- Filtered objects in an abelian category have cokernels. -/
@[stacks 0122]
noncomputable instance hasCokernels [Abelian C] : HasCokernels (FilteredObject C) where
  has_colimit f := HasColimit.mk ⟨_, Hom.toCokernelIsColimit f⟩

section ReusableInference

variable (C : Type u) [Category.{v} C] [Abelian C]

#synth HasFiniteLimits (FilteredObject C)
#synth HasFiniteColimits (FilteredObject C)

end ReusableInference

end CategoryTheory.FilteredObject
