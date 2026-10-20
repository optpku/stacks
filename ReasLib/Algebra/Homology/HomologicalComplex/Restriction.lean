module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of scalars on homological complexes

This leaf owns the concrete restriction of a module-valued homological complex along a ring
homomorphism.  Properties of the restricted complex belong in downstream termwise-property leaves.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace HomologicalComplex

variable {R : Type u} {A : Type v} [Ring R] [Ring A]
variable {ι : Type w} {c : ComplexShape ι}

/-- Stacks `0E1U`: restriction of a module-valued homological complex along an explicit ring
homomorphism. -/
@[stacks 0E1U "restriction of a complex along a ring map"]
abbrev restrictScalarsAlong
    (σ : R →+* A) (K : HomologicalComplex (ModuleCat A) c) :
    HomologicalComplex (ModuleCat R) c :=
  ((ModuleCat.restrictScalars σ).mapHomologicalComplex c).obj K

/-- Stacks `0E1U`: restriction of a morphism of module-valued homological complexes along an
explicit ring homomorphism. -/
@[stacks 0E1U "restriction of a complex morphism along a ring map"]
abbrev restrictScalarsMap
    (σ : R →+* A) {K L : HomologicalComplex (ModuleCat A) c} (f : K ⟶ L) :
    K.restrictScalarsAlong σ ⟶ L.restrictScalarsAlong σ :=
  ((ModuleCat.restrictScalars σ).mapHomologicalComplex c).map f

end HomologicalComplex
