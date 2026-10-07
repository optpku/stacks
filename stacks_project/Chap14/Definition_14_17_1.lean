module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Finiteness
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Representability
import StacksCheckRecall

@[expose] public section

/-!
@stack 017I

# Source-facing bridge for Definition 14.17.1

The simplicial mapping object and its universal property are owned by the assumption-minimal
`SimplicialObject.InternalHom.Representability` layer in ReasLib.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe uS vC uC

variable {C : Type uC} [Category.{vC} C]
variable (U : SSet.{uS}) (T : SimplicialObject C)
variable [HasBinaryCoproducts C] [U.ObjFinite] [U.Nonempty]
variable {M W : SimplicialObject C}
variable (R : (SimplicialObject.internalHom.presheaf U T).RepresentableBy M)

/- The represented source presheaf sends `W` to morphisms from the `U`-copower of `W` into
`T`. -/
#check (SimplicialObject.internalHom.presheaf U T :
  (SimplicialObject C)ᵒᵖ ⥤ Type vC)

/- Definition 14.17.1: an internal mapping object is any object representing morphisms from the
`U`-copower, functorially in the source simplicial object. -/
@[stacks 017I "Definition 14.17.1: universal property"]
#check (R.homEquiv :
  (W ⟶ M) ≃ (SimplicialObject.copower U W ⟶ T))

section Canonical

variable [SimplicialObject.HasInternalHom U T]

/- ReasLib chooses a canonical representing object when the corresponding representability
instance is available. -/
#check (SimplicialObject.internalHom U T : SimplicialObject C)

/- The chosen object exposes the same reusable `RepresentableBy` universal property. -/
#check ((SimplicialObject.internalHom.presheaf U T).representableBy :
  (SimplicialObject.internalHom.presheaf U T).RepresentableBy
    (SimplicialObject.internalHom U T))

/- Canonical users enter through the Hom equivalence rather than unpacking the chosen
representation. -/
#check (SimplicialObject.internalHom.homEquiv U T W :
  (W ⟶ SimplicialObject.internalHom U T) ≃
    (SimplicialObject.copower U W ⟶ T))

end Canonical
