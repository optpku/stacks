/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap71.Lemma_71_2_1_WeakAss

/-!
# Weakly associated points of modules on algebraic spaces

A point of an algebraic space is weakly associated to a module when the
maximal ideal of the étale local ring is weakly associated to the module
stalk. The weakly associated locus of the space is that of `𝒪_X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A point of `|X|` is weakly associated to an `𝒪_X`-module when the maximal
ideal of the étale local ring is weakly associated to the module stalk. -/
def weaklyAssociatedAt (F : X.Modules) (x : Points X) : Prop :=
  etaleStalkWeakAss F x

/-- The set of weakly associated points of an `𝒪_X`-module. -/
def weakAss (F : X.Modules) : Set (Points X) :=
  F.weaklyAssociatedAt

/-- Membership in `F.weakAss` is the pointwise weakly-associated-point predicate. -/
theorem mem_weakAss_iff (F : X.Modules) (x : Points X) :
    x ∈ F.weakAss ↔ F.weaklyAssociatedAt x :=
  sorry

/-- The pointwise weakly-associated-point predicate is the étale-stalk condition. -/
theorem weaklyAssociatedAt_iff_etaleStalkWeakAss (F : X.Modules) (x : Points X) :
    weaklyAssociatedAt F x ↔ etaleStalkWeakAss F x :=
  sorry

/-- For a quasi-coherent module, weak association is equivalent to the condition on some
étale scheme chart. -/
theorem weaklyAssociatedAt_iff_existsEtaleWeakAss (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) :
    weaklyAssociatedAt F x ↔ existsEtaleWeakAss F x :=
  sorry

/-- For a quasi-coherent module, weak association is equivalent to the condition on every
étale scheme chart. -/
theorem weaklyAssociatedAt_iff_forallEtaleWeakAss (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) :
    weaklyAssociatedAt F x ↔ forallEtaleWeakAss F x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The weakly associated points of an algebraic space are those of its structure sheaf. -/
abbrev weakAss : Set (Points X) :=
  Modules.weakAss (SheafOfModules.unit (structureSheaf X) : X.Modules)

/-- A point of an algebraic space is weakly associated when it is weakly associated
to the structure sheaf. -/
abbrev weaklyAssociatedAt (x : Points X) : Prop :=
  Modules.weaklyAssociatedAt (SheafOfModules.unit (structureSheaf X) : X.Modules) x

/-- Membership in `X.weakAss` is weak association of the structure sheaf. -/
theorem mem_weakAss_iff (x : Points X) :
    x ∈ X.weakAss ↔
      Modules.weaklyAssociatedAt (SheafOfModules.unit (structureSheaf X) : X.Modules) x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
