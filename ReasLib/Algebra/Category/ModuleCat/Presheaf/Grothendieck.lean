/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Notation
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Grothendieck

@[expose] public section

/-!
# Grothendieck Abelian Presheaf Module Categories

This leaf owns the Grothendieck-abelian structure of presheaves of modules over an arbitrary
ring-valued presheaf. The generic functorial-injective-embedding bridge is imported directly, so
downstream users obtain that structure without rebuilding separators or local instances.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace PresheafOfModules

/-- Presheaves of modules over a ring-valued presheaf form a Grothendieck abelian category. This
is the shared owner for their functorial injective embeddings. -/
@[stacks 0142, stacks 01DV "Grothendieck-abelian owner"]
instance isGrothendieckAbelian
    {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v}) :
    IsGrothendieckAbelian.{max u v} (PresheafOfModules.{max u v} 𝒪) := sorry

end PresheafOfModules

section

variable {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v})

-- The Grothendieck instance supplies a separator; reserve `PresheafOfModules.hasSeparator`
-- for the upstream instance in `Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator`.
#synth HasSeparator (PresheafOfModules.{max u v} 𝒪)
#synth IsGrothendieckAbelian.{max u v} (PresheafOfModules.{max u v} 𝒪)
#synth HasFunctorialInjectives (PresheafOfModules.{max u v} 𝒪)
#synth EnoughInjectives (PresheafOfModules.{max u v} 𝒪)

end
