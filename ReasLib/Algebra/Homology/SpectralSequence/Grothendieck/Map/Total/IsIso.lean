module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.IsIso
public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Total

/-!
# Isomorphisms in the total Grothendieck spectral-sequence category

The total category remembers both the derived base arrow and the filtered realization map.
These instances expose the corresponding projection-wise `IsIso` facts and reconstruct a total
isomorphism from them.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Total

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]
variable {G : B ⥤ C} [G.Additive]
variable {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
variable {S T : Total G RF RGF}

/-- A total morphism is an isomorphism when both its base and filtered components are. -/
@[stacks 015N "isomorphism transport in the total Grothendieck category"]
noncomputable instance hom_isIso (f : S ⟶ T) [IsIso f.base]
    [IsIso f.map.filteredMap] : IsIso f := sorry

/-- The base component of an isomorphic total morphism is an isomorphism. -/
@[stacks 015N "base isomorphism of a total Grothendieck morphism"]
noncomputable instance base_isIso (f : S ⟶ T) [IsIso f] : IsIso f.base := sorry

/-- The filtered component of an isomorphic total morphism is an isomorphism. -/
@[stacks 015N "filtered-component isomorphism of a total Grothendieck morphism"]
noncomputable instance filteredMap_isIso (f : S ⟶ T) [IsIso f] :
    IsIso f.map.filteredMap := sorry

variable (f : S ⟶ T) [IsIso f]

#synth IsIso f.base
#synth IsIso f.map.filteredMap
#synth IsIso f.map.sequenceMap

variable (p : ℕ) (q n : ℤ)

#synth IsIso (pageTwoMap G RF f.base p q)
#synth IsIso (abutmentMap RGF f.base n)

variable (g : S ⟶ T) [IsIso g.base] [IsIso g.map.filteredMap]

#synth IsIso g

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Total
