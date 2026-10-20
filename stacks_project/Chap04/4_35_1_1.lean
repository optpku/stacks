/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (p : S ⥤ C) {U V W : C} {x y z z' : S}
variable (f : V ⟶ U) (g : W ⟶ V)
variable (φ : y ⟶ x) (ψ : z ⟶ y) (γ : z' ⟶ x)
variable [p.IsStronglyCartesian f φ] [p.IsStronglyCartesian g ψ]
variable [p.IsStronglyCartesian (g ≫ f) γ]

/-
The diagram compares the composite lift `ψ ≫ φ` with the direct lift `γ`, both over
`g ≫ f`. The canonical same-base owner `IsCartesian.domainUniqueUpToIso`, specialized in that
order, gives `z' ≅ z`; its hom/inverse factorization lemmas and `IsHomLift` instances give the
two dotted arrows and their verticality. `IsStronglyCartesian.comp` supplies cartesianness of
`ψ ≫ φ`. The more general `IsStronglyCartesian.domainIsoOfBaseIso` would introduce an
irrelevant base isomorphism. This specialization matches `Functor.Cleavage.Reindex.compIsoApp`
and leaves downstream users on the canonical comparison API instead of four diagram wrappers.
-/

/- 4.35.1.1: for the strongly cartesian lifts `φ`, `ψ`, and `γ`, the canonical isomorphism
`z' ≅ z` supplies the two dotted vertical comparison arrows in the displayed diagram. -/
@[stacks 03WP "direct-versus-composite cartesian lift comparison"]
#check (IsCartesian.domainUniqueUpToIso p (g ≫ f) (ψ ≫ φ) γ : z' ≅ z)

end CategoryTheory
