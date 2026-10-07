module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Functor.IsIso
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Category.IsIso

/-!
# Isomorphism views of Cartan--Eilenberg total maps

Totalization and the standard filtered-total constructions preserve isomorphisms of
Cartan--Eilenberg resolution maps.  The declarations are instances so a comparison argument can
move from a resolution map to any total view without manually rebuilding `IsIso` evidence.
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

/-- Totalization sends an isomorphism of resolving double complexes to an isomorphism of total
cochain complexes. -/
@[stacks 015J "isomorphism of Cartan-Eilenberg total maps"]
instance total_isIso (f : Map I J) [IsIso f.hom] : IsIso (total f) := sorry

/-- The bounded-below total map of an isomorphism of resolutions is an isomorphism. -/
@[stacks 015J "isomorphism of bounded-below Cartan-Eilenberg total maps"]
instance totalPlus_isIso (f : Map I J) [IsIso f.hom] : IsIso (totalPlus f) := sorry

section Mapped

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- A mapped totalization sends an isomorphism of resolutions to an isomorphism. -/
@[stacks 015J "isomorphism of mapped Cartan-Eilenberg total maps"]
instance mappedTotal_isIso (f : Map I J) (F : A ⥤ B) [F.Additive]
    [IsIso f.hom] : IsIso (mappedTotal f F) := sorry

namespace First

/-- The first filtered total map of an isomorphism of resolutions is an isomorphism. -/
@[stacks 015J "isomorphism of first-filtered Cartan-Eilenberg total maps"]
instance filteredTotal_isIso (f : Map I J) (F : A ⥤ B) [F.Additive]
    [IsIso f.hom] : IsIso (filteredTotal f F) := sorry

end First

namespace Second

/-- The second filtered total map of an isomorphism of resolutions is an isomorphism. -/
@[stacks 015J "isomorphism of second-filtered Cartan-Eilenberg total maps"]
instance filteredTotal_isIso (f : Map I J) (F : A ⥤ B) [F.Additive]
    [IsIso f.hom] : IsIso (filteredTotal f F) := sorry

end Second

end Mapped

section Bundled

variable {X Y : CochainComplex.CartanEilenbergResolution.Bundled A}
variable (f : X ⟶ Y) [IsIso f]

#synth IsIso (total f)
#synth IsIso (totalPlus f)

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive]

#synth IsIso (mappedTotal f F)
#synth IsIso (First.filteredTotal f F)
#synth IsIso (Second.filteredTotal f F)

end Bundled

end CochainComplex.CartanEilenbergResolution.Map
