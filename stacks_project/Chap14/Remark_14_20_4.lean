module

public import ReasLib.AlgebraicTopology.Cech.Nerve.Augmentation
import StacksCheckRecall

/-!
@stack 018J

# Remark 14.20.4 compatibility facade

The canonical factorization of an augmentation through the Cech nerve of its degree-zero
component is owned by ReasLib.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {X : C} {V : SimplicialObject C}
variable (epsilon : V ⟶ (const C).obj X)

/- Remark 14.20.4: the canonical map to the Cech nerve of an augmentation. -/
@[stacks 018J]
#check (Augmentation.Cech.hom epsilon :
  V ⟶ (Arrow.mk (epsilon.app (op ⦋0⦌))).cechNerve)

#check Augmentation.Cech.hom.app_zero_π epsilon
#check Augmentation.Cech.hom.comp_augmentation epsilon

end CategoryTheory.SimplicialObject
