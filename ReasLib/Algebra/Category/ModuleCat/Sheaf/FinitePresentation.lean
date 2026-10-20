/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely presented sheaves of modules

This file owns kernel and cokernel closure statements for Mathlib's
`SheafOfModules.IsFinitePresentation` predicate.  The results are formulated over an arbitrary
sheaf of rings on a site, independently of ringed-space specializations.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v w

namespace SheafOfModules.IsFinitePresentation

section IsoTransport

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Finite presentation transports across an isomorphism of module sheaves.  The property owner
is Mathlib's `SheafOfModules.IsFinitePresentation`; this named bridge keeps comparison proofs
independent of the chosen local presentation data. -/
@[stacks 01BN "isomorphism transport"]
theorem of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFinitePresentation] :
    N.IsFinitePresentation := sorry

/-- Finite presentation is invariant under an isomorphism of module sheaves. -/
@[stacks 01BN "isomorphism invariance"]
theorem iff_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) :
    M.IsFinitePresentation ↔ N.IsFinitePresentation := sorry

end IsoTransport

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The cokernel of a map from a finite-type
module sheaf to a finitely presented module sheaf is finitely presented. -/
@[stacks 0H96, stacks 0H98]
theorem cokernel {G F : SheafOfModules.{u} R} (φ : G ⟶ F)
    [G.IsFiniteType] [F.IsFinitePresentation] :
    (Limits.cokernel φ).IsFinitePresentation := sorry

/-- The kernel of an epimorphism from a
finite-type module sheaf to a finitely presented module sheaf is finite type. -/
@[stacks 01BP "finite-type source", stacks 082T]
theorem kernel_of_epi {G F : SheafOfModules.{u} R} (θ : G ⟶ F)
    [Epi θ] [G.IsFiniteType] [F.IsFinitePresentation] :
    (Limits.kernel θ).IsFiniteType := sorry

/-- In a short exact sequence, a finite-type left term
and finitely presented middle term give a finitely presented right term. -/
@[stacks 0H96 "short-exact form"]
theorem cokernel_of_shortExact
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    [S.X₁.IsFiniteType] [S.X₂.IsFinitePresentation] :
    S.X₃.IsFinitePresentation := sorry

/-- In a short exact sequence, a finite-type middle term
and finitely presented right term give a finite-type left term. -/
@[stacks 01BP "short-exact form"]
theorem kernel_of_shortExact
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    [S.X₂.IsFiniteType] [S.X₃.IsFinitePresentation] :
    S.X₁.IsFiniteType := sorry

end SheafOfModules.IsFinitePresentation
