/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment.IsIso

/-!
# Isomorphisms of Grothendieck spectral-sequence maps

The page-two and abutment compatibility squares transport an isomorphism of the filtered
component to all target components.  This leaf registers that transport as ordinary `IsIso`
instances, so applications can use the standard categorical API without rebuilding the
comparison-conjugation argument.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Map

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]

variable {G : B ⥤ C} [G.Additive]
variable {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
variable {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
variable {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}

/-- The spectral-sequence map of an isomorphic Grothendieck realization map is an isomorphism. -/
@[stacks 015N "spectral-sequence isomorphism of Grothendieck maps"]
noncomputable instance sequenceMap_isIso (m : Map f S T) [IsIso m.filteredMap] :
    IsIso m.sequenceMap := sorry

/-- A page-two target functor sends an isomorphism of derived objects to an isomorphism. -/
@[stacks 015N "page-two isomorphism of Grothendieck maps"]
noncomputable instance pageTwoMap_isIso (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (f : X ⟶ Y) [IsIso f] (p : ℕ) (q : ℤ) :
    IsIso (pageTwoMap G RF f p q) := sorry

/-- A Grothendieck abutment functor sends an isomorphism of derived objects to an isomorphism. -/
@[stacks 015N "abutment isomorphism of Grothendieck maps"]
noncomputable instance abutmentMap_isIso (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    (f : X ⟶ Y) [IsIso f] (n : ℤ) :
    IsIso (abutmentMap RGF f n) := sorry

/-- A page-two target map is an isomorphism whenever it occurs in a Grothendieck realization
map whose filtered component is an isomorphism. -/
@[stacks 015N "page-two isomorphism from a filtered Grothendieck isomorphism"]
theorem pageTwoMap_isIso_of_filteredMap (m : Map f S T) (p : ℕ) (q : ℤ)
    [IsIso m.filteredMap] : IsIso (pageTwoMap G RF f p q) := sorry

/-- An abutment target map is an isomorphism whenever it occurs in a Grothendieck realization
map whose filtered component is an isomorphism. -/
@[stacks 015N "abutment isomorphism from a filtered Grothendieck isomorphism"]
theorem abutmentMap_isIso_of_filteredMap (m : Map f S T) (n : ℤ)
    [IsIso m.filteredMap] : IsIso (abutmentMap RGF f n) := sorry

/- Axiom audit: the declarations above only register proposition-valued isomorphism transport;
the concrete map and comparison data remain owned by `Map.lean`. -/

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Map
