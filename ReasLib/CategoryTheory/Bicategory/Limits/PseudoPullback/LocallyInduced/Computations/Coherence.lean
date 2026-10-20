module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Computations.Action
import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Pseudofunctor.Computations.Coherence

/-!
# Coherence computations for locally induced pseudopullback cones

This leaf exposes the identity and composition comparisons of the locally induced forgetful cone
pseudofunctor and their ambient apex cells.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uA uB vB wB

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {A : Type uA} {B : Type uB} [Bicategory.{wB, vB} B]
variable {baseObj : A → B} {Q : Bicategory.HomProperty baseObj} [Q.IsMultiplicative]
variable {x y z : Bicategory.LocallyInducedBicategory B baseObj Q}
variable {f : x ⟶ z} {g : y ⟶ z}

/-- The unit comparison of the locally induced forgetful cone pseudofunctor is the canonical
readable mapped-cone unit comparison. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.mapId
    (P : PseudoPullbackCone f g) :
    (forgetLocallyInduced.pseudofunctor f g).mapId P =
      Pseudofunctor.mapPseudoPullbackCone.mapId
        ((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor) P := sorry

/-- The composition comparison of the locally induced forgetful cone pseudofunctor is the
canonical readable mapped-cone composition comparison. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.mapComp
    {P R S : PseudoPullbackCone f g} (u : P ⟶ R) (v : R ⟶ S) :
    (forgetLocallyInduced.pseudofunctor f g).mapComp u v =
      Pseudofunctor.mapPseudoPullbackCone.mapComp
        ((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor) u v := sorry

/-- The apex cell of the forward unit comparison of locally induced cone forgetting is the
forward unit comparison of the ambient forgetful pseudofunctor. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.mapId.hom.apex
    (P : PseudoPullbackCone f g) :
    PseudoPullbackCone.map₂
        ((forgetLocallyInduced.pseudofunctor f g).mapId P).hom =
      (((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor).mapId P.pt).hom := sorry

/-- The apex cell of the inverse unit comparison of locally induced cone forgetting is the
inverse unit comparison of the ambient forgetful pseudofunctor. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.mapId.inv.apex
    (P : PseudoPullbackCone f g) :
    PseudoPullbackCone.map₂
        ((forgetLocallyInduced.pseudofunctor f g).mapId P).inv =
      (((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor).mapId P.pt).inv := sorry

/-- The apex cell of the forward composition comparison of locally induced cone forgetting is
the forward composition comparison of the ambient forgetful pseudofunctor. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.mapComp.hom.apex
    {P R S : PseudoPullbackCone f g} (u : P ⟶ R) (v : R ⟶ S) :
    PseudoPullbackCone.map₂
        ((forgetLocallyInduced.pseudofunctor f g).mapComp u v).hom =
      (((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor).mapComp
        (PseudoPullbackCone.map u) (PseudoPullbackCone.map v)).hom := sorry

/-- The apex cell of the inverse composition comparison of locally induced cone forgetting is
the inverse composition comparison of the ambient forgetful pseudofunctor. -/
@[simp]
theorem forgetLocallyInduced.pseudofunctor.mapComp.inv.apex
    {P R S : PseudoPullbackCone f g} (u : P ⟶ R) (v : R ⟶ S) :
    PseudoPullbackCone.map₂
        ((forgetLocallyInduced.pseudofunctor f g).mapComp u v).inv =
      (((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor).mapComp
        (PseudoPullbackCone.map u) (PseudoPullbackCone.map v)).inv := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
