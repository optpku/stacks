module

public import ReasLib.CategoryTheory.Filtration.Biproduct
public import ReasLib.CategoryTheory.Filtration.Strict
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Biproduct Descents

Strict epimorphisms remain strict after adjoining an arbitrary second summand map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasImages C] [HasPullbacks C]
  [HasEqualizers C] [HasBinaryBiproducts C] [Balanced C]
variable {A B D : FilteredObject C}

/-- A biproduct descent is epic on underlying objects when its first component is epic. -/
instance epi_biprodDesc_hom_of_epi_left (f : A ⟶ D) (g : B ⟶ D) [Epi f.hom] :
    Epi (biprod.desc f g).hom := sorry

/-- If `f : A ⟶ D` is a strict epimorphism and `g : B ⟶ D` is arbitrary, the induced
biproduct descent `A ⊞ B ⟶ D` is strict. -/
@[stacks 05SL]
theorem strict_biprodDesc (f : A ⟶ D) (g : B ⟶ D) [Epi f.hom] (hf : Strict f) :
    Strict (biprod.desc f g) := sorry

end CategoryTheory.FilteredObject.Hom
