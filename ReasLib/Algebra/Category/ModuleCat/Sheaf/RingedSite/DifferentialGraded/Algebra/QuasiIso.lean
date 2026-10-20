/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-isomorphisms of differential graded algebra sheaves

A morphism of differential graded algebra sheaves is a quasi-isomorphism when its underlying
cochain map is one.  This file records the predicate as a `MorphismProperty`, together with the
closure properties needed by localization and change-of-rings constructions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MorphismProperty
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

/-- A morphism of differential graded algebra sheaves is a quasi-isomorphism when its underlying
cochain map is a quasi-isomorphism. -/
@[stacks 0FTZ "quasi-isomorphisms of differential graded algebra sheaves"]
def quasiIso : MorphismProperty DGA(𝒪) :=
  fun _ _ f ↦ _root_.QuasiIso f.hom

namespace QuasiIso

/-- Membership in the DGA quasi-isomorphism property is the canonical quasi-isomorphism predicate
on the underlying cochain map. -/
theorem iff_underlying {A B : DGA(𝒪)} (f : A ⟶ B) :
    quasiIso f ↔ _root_.QuasiIso f.hom := sorry

/-- DGA quasi-isomorphisms contain identity morphisms. -/
instance containsIdentities :
    (quasiIso (𝒪 := 𝒪)).ContainsIdentities := sorry

/-- DGA quasi-isomorphisms are closed under composition. -/
instance isMultiplicative :
    (quasiIso (𝒪 := 𝒪)).IsMultiplicative := sorry

/-- DGA quasi-isomorphisms satisfy the two-out-of-three property. -/
instance hasTwoOutOfThree :
    (quasiIso (𝒪 := 𝒪)).HasTwoOutOfThreeProperty := sorry

/-- DGA quasi-isomorphisms are stable under retracts. -/
instance isStableUnderRetracts :
    (quasiIso (𝒪 := 𝒪)).IsStableUnderRetracts := sorry

end QuasiIso

end SheafOfModules.RingedSite.DifferentialGradedAlgebra

end
