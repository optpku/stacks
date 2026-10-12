/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise regular scalar actions on module-valued complexes

This lightweight module owns scalar regularity degree by degree for an arbitrary-shaped
module-valued homological complex.  It deliberately does not import projectivity, finiteness,
or Noetherian homology infrastructure.
@stack 0F7P
@stack 0GSQ
-/

@[expose] public section

universe u v

namespace HomologicalComplex

variable {R : Type u} [Ring R]
variable {ι : Type v} {c : ComplexShape ι}

/-- Multiplication by `r` is injective on every term of a module-valued homological complex. -/
@[stacks 0F7P "termwise regular scalar action",
  stacks 0GSQ "termwise regular scalar on a Bockstein complex"]
def IsTermwiseSMulRegular (K : HomologicalComplex (ModuleCat R) c) (r : R) : Prop :=
  ∀ i : ι, IsSMulRegular (K.X i) r

/-- The bundled category of module-valued complexes on which a scalar acts regularly termwise. -/
@[stacks 0F7P "termwise regular complex domain",
  stacks 0GSQ "termwise regular Bockstein domain"]
abbrev RegularDomain (r : R) :=
  CategoryTheory.ObjectProperty.FullSubcategory
    (IsTermwiseSMulRegular (r := r) :
      CategoryTheory.ObjectProperty (HomologicalComplex (ModuleCat R) c))

/-- Unfolding termwise scalar regularity exposes injectivity in every degree. -/
theorem isTermwiseSMulRegular_iff (K : HomologicalComplex (ModuleCat R) c) (r : R) :
    K.IsTermwiseSMulRegular r ↔ ∀ i : ι, IsSMulRegular (K.X i) r := sorry

namespace IsTermwiseSMulRegular

variable {K : HomologicalComplex (ModuleCat R) c} {r : R}

/-- A termwise regular scalar acts regularly in each specified degree. -/
theorem degree (hK : K.IsTermwiseSMulRegular r) (i : ι) :
    IsSMulRegular (K.X i) r := sorry

end IsTermwiseSMulRegular

end HomologicalComplex
