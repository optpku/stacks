module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Variance
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.Comparison
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.Pullback.Map

/-!
# Objectwise target naturality of the internal-hom pushout comparison
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom.pushout.comparison

variable {C : Type uC} [Category.{vC} C]
variable {U V W : SSet.{uS}} (a : U ⟶ V) (b : U ⟶ W)
variable [HasCopowers U C] [HasCopowers V C] [HasCopowers W C]
variable [HasCopowers (pushout a b) C]
variable {T T' : SimplicialObject C} (p : T ⟶ T')
variable [HasInternalHom U T] [HasInternalHom V T] [HasInternalHom W T]
variable [HasInternalHom (pushout a b) T]
variable [HasInternalHom U T'] [HasInternalHom V T'] [HasInternalHom W T']
variable [HasInternalHom (pushout a b) T']
/-- The internal-hom pushout comparison commutes with postcomposition in the
target, with the right side expressed by the canonical map between pullbacks. -/
@[reassoc, stacks 017N "target naturality of the internal-hom pushout comparison"]
theorem naturality :
    postcomp (pushout a b) p ≫ pushout.comparison a b T' =
      pushout.comparison a b T ≫ pushout.pullback.map a b p := sorry

end CategoryTheory.SimplicialObject.internalHom.pushout.comparison
