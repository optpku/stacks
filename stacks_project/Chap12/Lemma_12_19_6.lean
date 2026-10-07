module

public import ReasLib.CategoryTheory.Filtration.Strict.BiproductDesc
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasImages C] [HasPullbacks C]
  [HasEqualizers C] [HasBinaryBiproducts C] [Balanced C]
variable {A B D : FilteredObject C} (f : A ⟶ D) (g : B ⟶ D) [Epi f.hom]

/- Lemma 12.19.6 [05SL]: adjoining an arbitrary summand map to a strict epimorphism preserves
strictness. -/
@[stacks 05SL]
#check (strict_biprodDesc f g : Strict f → Strict (biprod.desc f g))

end CategoryTheory.FilteredObject.Hom
