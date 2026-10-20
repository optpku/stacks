module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Extension.Construction
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Extension.PartialRightAdjoint
import StacksCheckRecall

/-!
@stack 0187

# Lemma 14.19.6 compatibility facade

The construction and its partial-adjoint consequence are owned by the matching-family API in
ReasLib.  Writing the source truncation level as `n + 1` records its positivity without carrying
an otherwise unused inequality parameter.
-/

@[expose] public section

open CategoryTheory Opposite
open SimplexCategory.Truncated
open SimplicialObject.Truncated.matching
open scoped Simplicial SimplexCategory.Truncated

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (U_succ : C)
variable (R :
  (SimplicialObject.Truncated.matching.FaceFamily.presheaf U).RepresentableBy U_succ)
variable (E : Extension R)
variable (V : SimplicialObject.Truncated C ((n + 1) + 1))
variable (g : V ⟶ E.obj)
variable (f :
  (SimplicialObject.Truncated.trunc C ((n + 1) + 1) (n + 1)).obj V ⟶ U)

/- Lemma 14.19.6 (1): a representing object for the next matching families of a positive-degree
truncated simplicial object admits a one-step extension with that object as its new top term. -/
@[stacks 0187 "Lemma 14.19.6 (1)"]
#check (Extension.nonempty R : Nonempty (Extension R))

/- Any chosen extension exposes the bundled old-part comparison used by the universal property. -/
#check (E.truncIso :
  (SimplicialObject.Truncated.trunc C ((n + 1) + 1) (n + 1)).obj E.obj ≅ U)

/- Lemma 14.19.6 (2): the extension represents morphisms from one-step truncated objects,
which is the stated right-adjoint universal property. -/
@[stacks 0187 "Lemma 14.19.6 (2)"]
#check (E.homEquiv :
  (V ⟶ E.obj) ≃
    ((SimplicialObject.Truncated.trunc C ((n + 1) + 1) (n + 1)).obj V ⟶ U))

/- Lemma 14.19.6 (2): the represented Hom equivalence is restriction followed by the
comparison with `U`. -/
@[stacks 0187 "Lemma 14.19.6 (2): Hom equivalence formula"]
#check (Extension.homEquiv.apply E g :
  E.homEquiv g =
    (SimplicialObject.Truncated.trunc C ((n + 1) + 1) (n + 1)).map g ≫
      E.truncIso.hom)

/- The inverse Hom equivalence reconstructs the unique extension whose restriction is the
prescribed morphism. -/
#check (Extension.homEquiv.symm_apply E f :
  (SimplicialObject.Truncated.trunc C ((n + 1) + 1) (n + 1)).map
      ((E.homEquiv (V := V)).symm f) ≫ E.truncIso.hom = f)

/- The same hypothesis gives an object in the source of mathlib's canonical partial right
adjoint to one-step truncation. -/
@[stacks 0187 "Lemma 14.19.6: partial right-adjoint source"]
#check (FaceFamily.partialRightAdjoint.source R.isRepresentable :
  (SimplicialObject.Truncated.trunc C ((n + 1) + 1) (n + 1)).PartialRightAdjointSource)

/- Its property is the corresponding partial-right-adjoint definedness statement. -/
#check (FaceFamily.partialRightAdjoint.objDefined R.isRepresentable :
  (SimplicialObject.Truncated.trunc C ((n + 1) + 1) (n + 1)).rightAdjointObjIsDefined U)

/- Any one-step extension is canonically isomorphic to the object selected by that partial right
adjoint. -/
#check (Extension.partialRightAdjoint.iso E :
  E.obj ≅
    (SimplicialObject.Truncated.trunc C ((n + 1) + 1) (n + 1)).partialRightAdjointObj
      (FaceFamily.partialRightAdjoint.source R.isRepresentable))

/- The comparison is characterized by its action on the universal element. -/
#check Extension.partialRightAdjoint.iso.hom_apply E

/- The inverse comparison has the symmetric universal-element formula. -/
#check Extension.partialRightAdjoint.iso.inv_apply E

end CategoryTheory
