module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Lift
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-! # Literal lifts into full-subbicategory two-fibre products

The square's two functors and invertible comparison supply all lift data.
Closure of the object property is needed only for the chosen apex membership.
-/

@[expose] public section

open CategoryTheory Bicategory ObjectProperty
open scoped Bicategory BasedFunctor

noncomputable section

universe u v w vB

namespace CategoryTheory.TwoFibreProduct

variable {C : Type u} [Category.{v} C]
variable {P : ObjectProperty
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X Y S : P.FullSubbicategory} {F : X ⟶ S} {G : Y ⟶ S}

/-- Lift a supplied cone by retaining its common base, both legs and comparison. -/
def lift (cone : PseudoPullbackCone F G) : cone.pt ⟶ apex F G :=
  InducedBicategory.mkHom
    (BasedCategory.PseudoPullback.lift F.hom G.hom cone.fst.hom cone.snd.hom
      (InducedBicategory.Iso.toAmbient cone.iso))

/-- The first leg comparison of the actual lift has identity components. -/
def lift.fstIso (cone : PseudoPullbackCone F G) : lift cone ≫ fst F G ≅ cone.fst :=
  InducedBicategory.isoMk
    (BasedCategory.PseudoPullback.lift.fstIso F.hom G.hom cone.fst.hom cone.snd.hom
      (InducedBicategory.Iso.toAmbient cone.iso))

/-- The second leg comparison of the actual lift has identity components. -/
def lift.sndIso (cone : PseudoPullbackCone F G) : lift cone ≫ snd F G ≅ cone.snd :=
  InducedBicategory.isoMk
    (BasedCategory.PseudoPullback.lift.sndIso F.hom G.hom cone.fst.hom cone.snd.hom
      (InducedBicategory.Iso.toAmbient cone.iso))

end CategoryTheory.TwoFibreProduct
