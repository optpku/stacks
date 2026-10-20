module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalHomology
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total.IsIso

/-!
# Isomorphism views of Cartan--Eilenberg total homology maps

Homology of a mapped total, or of either standard filtered total, inherits isomorphisms from the
underlying resolution map.  This leaf keeps those consequences available without importing any
derived-category comparison layer.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- Mapped-total homology sends an isomorphism of resolutions to an isomorphism. -/
@[stacks 015J "isomorphism on Cartan-Eilenberg mapped-total homology"]
instance mappedTotalHomology_isIso (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ)
    [IsIso f.hom] : IsIso (mappedTotalHomology f F n) := sorry

namespace First

/-- First filtered-total homology sends an isomorphism of resolutions to an isomorphism. -/
@[stacks 015J "isomorphism on first Cartan-Eilenberg filtered homology"]
instance filteredTotalHomology_isIso (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ)
    [IsIso f.hom] : IsIso (filteredTotalHomology f F n) := sorry

end First

namespace Second

/-- Second filtered-total homology sends an isomorphism of resolutions to an isomorphism. -/
@[stacks 015J "isomorphism on second Cartan-Eilenberg filtered homology"]
instance filteredTotalHomology_isIso (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ)
    [IsIso f.hom] : IsIso (filteredTotalHomology f F n) := sorry

end Second

section Bundled

variable {X Y : CochainComplex.CartanEilenbergResolution.Bundled A}
variable (f : X ⟶ Y) [IsIso f]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] (n : ℤ)

#synth IsIso (mappedTotalHomology f F n)
#synth IsIso (First.filteredTotalHomology f F n)
#synth IsIso (Second.filteredTotalHomology f F n)

end Bundled

end CochainComplex.CartanEilenbergResolution.Map
