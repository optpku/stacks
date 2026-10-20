module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally-induced pseudopullback-cone lifts

This leaf owns the concrete lift of an ambient readable pseudopullback cone into a locally
induced bicategory over an object-property full subbicategory. Besides apex membership, the two
projection membership proofs are explicit inputs. The locally induced bilimit criterion is
separate because restricting `1`-morphisms can change the universal property.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u w' v' u'

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {C : Type u'} [Bicategory.{w', v'} C]
variable (P : ObjectProperty C)

variable (Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1))
variable [Q.IsMultiplicative]
variable {X Y Z : Bicategory.LocallyInducedBicategory C
  (fun X : P.FullSubbicategory ↦ X.1) Q}
variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- Lift an ambient pseudopullback cone to a locally induced bicategory. Besides membership
of the apex in `P`, both projections must satisfy the selected hom property `Q`. -/
@[stacks 02XQ "locally induced lift of a pseudo-pullback cone"]
def inLocallyInduced
    (S : PseudoPullbackCone f.obj g.obj) (hS : P S.pt)
    (hfst : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) X S.fst)
    (hsnd : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) Y S.snd) :
    PseudoPullbackCone f g where
  pt := ObjectProperty.FullSubbicategory.mk P S.pt hS
  fst := Bicategory.LocallyInducedBicategory.mkHom
      (F := fun X : P.FullSubbicategory ↦ X.1) (Q := Q) S.fst hfst
  snd := Bicategory.LocallyInducedBicategory.mkHom
      (F := fun X : P.FullSubbicategory ↦ X.1) (Q := Q) S.snd hsnd
  iso := (Q _ _).isoMk S.iso

/-- The ambient apex of a pseudopullback cone lifted to a locally induced bicategory is the
original ambient apex. -/
@[simp]
theorem inLocallyInduced.pt.obj
    (S : PseudoPullbackCone f.obj g.obj) (hS : P S.pt)
    (hfst : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) X S.fst)
    (hsnd : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) Y S.snd) :
    (inLocallyInduced P Q S hS hfst hsnd).pt.1 = S.pt := sorry

/-- The ambient first projection of a pseudopullback cone lifted to a locally induced
bicategory is the original first projection. -/
@[simp]
theorem inLocallyInduced.fst.obj
    (S : PseudoPullbackCone f.obj g.obj) (hS : P S.pt)
    (hfst : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) X S.fst)
    (hsnd : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) Y S.snd) :
    (inLocallyInduced P Q S hS hfst hsnd).fst.obj = S.fst := sorry

/-- The ambient second projection of a pseudopullback cone lifted to a locally induced
bicategory is the original second projection. -/
@[simp]
theorem inLocallyInduced.snd.obj
    (S : PseudoPullbackCone f.obj g.obj) (hS : P S.pt)
    (hfst : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) X S.fst)
    (hsnd : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) Y S.snd) :
    (inLocallyInduced P Q S hS hfst hsnd).snd.obj = S.snd := sorry

/-- The comparison isomorphism of a pseudopullback cone lifted to a locally induced bicategory is
the ambient comparison isomorphism regarded in the selected hom category. -/
@[simp]
theorem inLocallyInduced.iso
    (S : PseudoPullbackCone f.obj g.obj) (hS : P S.pt)
    (hfst : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) X S.fst)
    (hsnd : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) Y S.snd) :
    (inLocallyInduced P Q S hS hfst hsnd).iso =
      (Q _ _).isoMk S.iso := sorry

/-- The ambient forward comparison cell of a pseudopullback cone lifted to a locally induced
bicategory is the original forward comparison cell. -/
@[simp]
theorem inLocallyInduced.iso.hom
    (S : PseudoPullbackCone f.obj g.obj) (hS : P S.pt)
    (hfst : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) X S.fst)
    (hsnd : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) Y S.snd) :
    (inLocallyInduced P Q S hS hfst hsnd).iso.hom.hom =
      S.iso.hom := sorry

/-- The ambient inverse comparison cell of a pseudopullback cone lifted to a locally induced
bicategory is the original inverse comparison cell. -/
@[simp]
theorem inLocallyInduced.iso.inv
    (S : PseudoPullbackCone f.obj g.obj) (hS : P S.pt)
    (hfst : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) X S.fst)
    (hsnd : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) Y S.snd) :
    (inLocallyInduced P Q S hS hfst hsnd).iso.inv.hom =
      S.iso.inv := sorry

/- Data audit (mathlib 4.32): `inLocallyInduced` stores the ambient apex, projections, and
comparison isomorphism explicitly. The membership proofs are the only additional inputs; no
carrier or morphism representative is selected by `sorry`. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
