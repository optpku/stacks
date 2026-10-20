/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit Derived Extension Models

A derived extension of scalars is represented by its functor together with an adjunction to the
canonical derived restriction functor.  Keeping this data explicit prevents a concrete functor or
base-change morphism from being selected from a mere existence proof.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A concrete derived extension-of-scalars functor along `σ`, characterized as a left adjoint to
derived restriction of scalars. -/
@[stacks 0BYX "explicit derived extension of scalars"]
structure DerivedExtension (σ : R →+* S) where
  /-- The chosen derived extension functor. -/
  toFunctor :
    DerivedCategory (ModuleCat.{u, u} R) ⥤ DerivedCategory (ModuleCat.{u, u} S)
  /-- Its extension-restriction adjunction. -/
  adjunction : toFunctor ⊣ derivedRestrictionOfScalars σ

namespace DerivedExtension

/-- Apply an explicit derived extension model to a derived module. -/
noncomputable abbrev obj (E : DerivedExtension (R := R) (S := S) σ)
    (K : DerivedCategory (ModuleCat.{u, u} R)) :
    DerivedCategory (ModuleCat.{u, u} S) :=
  E.toFunctor.obj K

/-- The Hom equivalence characterizing an explicit derived extension model. -/
noncomputable abbrev homEquiv (E : DerivedExtension (R := R) (S := S) σ)
    (K : DerivedCategory (ModuleCat.{u, u} R))
    (L : DerivedCategory (ModuleCat.{u, u} S)) :
    (E.obj K ⟶ L) ≃ (K ⟶ (derivedRestrictionOfScalars σ).obj L) :=
  E.adjunction.homEquiv K L

/-- Transpose a morphism into derived restriction to a morphism out of derived extension. -/
@[stacks 0BYX "derived extension transpose"]
noncomputable def transpose (E : DerivedExtension (R := R) (S := S) σ)
    {K : DerivedCategory (ModuleCat.{u, u} R)}
    {L : DerivedCategory (ModuleCat.{u, u} S)}
    (f : K ⟶ (derivedRestrictionOfScalars σ).obj L) : E.obj K ⟶ L :=
  (E.homEquiv K L).symm f

/-- Transpose a morphism out of derived extension back into derived restriction. -/
noncomputable def untranspose (E : DerivedExtension (R := R) (S := S) σ)
    {K : DerivedCategory (ModuleCat.{u, u} R)}
    {L : DerivedCategory (ModuleCat.{u, u} S)}
    (f : E.obj K ⟶ L) : K ⟶ (derivedRestrictionOfScalars σ).obj L :=
  E.homEquiv K L f

/-- Any two explicit derived extension models along the same ring map are canonically naturally
isomorphic, by uniqueness of a left adjoint to derived restriction. -/
@[stacks 0BYX "uniqueness of explicit derived extension"]
noncomputable def iso (E F : DerivedExtension (R := R) (S := S) σ) :
    E.toFunctor ≅ F.toFunctor :=
  E.adjunction.leftAdjointUniq F.adjunction

/-- The canonical isomorphism between two extension models commutes with transposition. -/
theorem iso_hom_transpose (E F : DerivedExtension (R := R) (S := S) σ)
    {K : DerivedCategory (ModuleCat.{u, u} R)}
    {L : DerivedCategory (ModuleCat.{u, u} S)}
    (f : K ⟶ (derivedRestrictionOfScalars σ).obj L) :
    (E.iso F).hom.app K ≫ F.transpose f = E.transpose f := sorry

/-- Invertibility of a transposed morphism is independent of the explicit derived extension
model. -/
theorem isIso_transpose_iff (E F : DerivedExtension (R := R) (S := S) σ)
    {K : DerivedCategory (ModuleCat.{u, u} R)}
    {L : DerivedCategory (ModuleCat.{u, u} S)}
    (f : K ⟶ (derivedRestrictionOfScalars σ).obj L) :
    IsIso (E.transpose f) ↔ IsIso (F.transpose f) := sorry

/-- Transposing and then untransposing recovers the original morphism. -/
@[simp]
theorem untranspose_transpose (E : DerivedExtension (R := R) (S := S) σ)
    {K : DerivedCategory (ModuleCat.{u, u} R)}
    {L : DerivedCategory (ModuleCat.{u, u} S)}
    (f : K ⟶ (derivedRestrictionOfScalars σ).obj L) :
    E.untranspose (E.transpose f) = f := sorry

/-- Untransposing and then transposing recovers the original morphism. -/
@[simp]
theorem transpose_untranspose (E : DerivedExtension (R := R) (S := S) σ)
    {K : DerivedCategory (ModuleCat.{u, u} R)}
    {L : DerivedCategory (ModuleCat.{u, u} S)}
    (f : E.obj K ⟶ L) :
    E.transpose (E.untranspose f) = f := sorry

end DerivedExtension

end CategoryTheory.ModuleCat
