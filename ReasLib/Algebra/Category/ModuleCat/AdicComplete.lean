/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# The category of adically complete modules

The full subcategory of adically complete modules has ordinary kernels and
completed cokernels for finitely generated ideals, but need not be abelian.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat.AdicComplete

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The object property of `R`-modules that are `I`-adically complete. -/
abbrev property : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ IsAdicComplete I M

/-- The full subcategory of `I`-adically complete `R`-modules. -/
abbrev category := (property I).FullSubcategory

/-- The inclusion of `I`-adically complete modules into all `R`-modules. -/
abbrev inclusion : category I ⥤ ModuleCat.{v} R := (property I).ι

/-- `I`-adic completeness is preserved by isomorphisms in `ModuleCat`. -/
instance property.isClosedUnderIsomorphisms :
    (property I).IsClosedUnderIsomorphisms := sorry

/-- The underlying linear map of a morphism of `I`-adically complete modules. -/
abbrev linearMap {X Y : category I} (f : X ⟶ Y) :
    (inclusion I).obj X →ₗ[R] (inclusion I).obj Y :=
  ((inclusion I).map f).hom

/-- The ordinary kernel of a morphism of `I`-adically complete modules is
`I`-adically complete when `I` is finitely generated. -/
theorem kernel_isAdicComplete (hI : I.FG) {X Y : category I} (f : X ⟶ Y) :
    IsAdicComplete I (LinearMap.ker (linearMap I f)) := sorry

/-- A finitely generated ideal gives the ordinary kernel of a morphism of
complete modules its canonical adic-completeness instance. -/
instance kernelIsAdicComplete [Fact I.FG] {X Y : category I} (f : X ⟶ Y) :
    IsAdicComplete I (LinearMap.ker (linearMap I f)) :=
  kernel_isAdicComplete I (Fact.out : I.FG) f

/-- The kernel object in the category of `I`-adically complete modules, given by
the ordinary kernel. -/
noncomputable def kernelObj (hI : I.FG) {X Y : category I} (f : X ⟶ Y) :
    category I :=
  ⟨ModuleCat.of R (LinearMap.ker (linearMap I f)), kernel_isAdicComplete I hI f⟩

/-- The ordinary cokernel of a morphism of `I`-adically complete modules. -/
abbrev ordinaryCokernel {X Y : category I} (f : X ⟶ Y) : ModuleCat.{v} R :=
  ModuleCat.of R ((inclusion I).obj Y ⧸ LinearMap.range (linearMap I f))

/-- The cokernel object in the category of `I`-adically complete modules, given by
the `I`-adic completion of the ordinary cokernel. -/
noncomputable def cokernelObj (hI : I.FG) {X Y : category I} (f : X ⟶ Y) :
    category I :=
  ⟨ModuleCat.of R (AdicCompletion I (ordinaryCokernel I f)),
    AdicCompletion.isAdicComplete hI⟩

/-- The canonical comparison from the ordinary cokernel to the completed cokernel. -/
noncomputable def cokernelComparison (hI : I.FG) {X Y : category I} (f : X ⟶ Y) :
    ordinaryCokernel I f ⟶ (inclusion I).obj (cokernelObj I hI f) :=
  ModuleCat.ofHom (AdicCompletion.of I (ordinaryCokernel I f))

/-- The category of `I`-adically complete `R`-modules has kernels when `I` is
finitely generated. -/
theorem hasKernels (hI : I.FG) : HasKernels (category I) := sorry

/-- A finitely generated ideal canonically gives the category of adically
complete modules kernels. -/
instance hasKernelsOfFG [Fact I.FG] : HasKernels (category I) :=
  hasKernels I (Fact.out : I.FG)

/-- The category of `I`-adically complete `R`-modules has cokernels when `I` is
finitely generated. -/
theorem hasCokernels (hI : I.FG) : HasCokernels (category I) := sorry

/-- A finitely generated ideal canonically gives the category of adically
complete modules cokernels. -/
instance hasCokernelsOfFG [Fact I.FG] : HasCokernels (category I) :=
  hasCokernels I (Fact.out : I.FG)

/-- There is a commutative Noetherian ring with a finitely generated ideal whose
category of adically complete modules is not abelian. -/
theorem exists_noetherian_not_abelian :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsNoetherianRing R) (I : Ideal R),
      I.FG ∧ ¬ Nonempty (Abelian (category I)) := sorry

end ModuleCat.AdicComplete
