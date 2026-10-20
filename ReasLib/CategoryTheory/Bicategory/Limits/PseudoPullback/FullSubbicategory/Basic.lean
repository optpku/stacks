/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Full-subbicategory pseudopullback-cone lifts

This leaf owns the concrete lift of a readable pseudopullback cone into an object-property full
subbicategory. The apex membership proof is the only extra input; all ambient `1`- and
`2`-morphism data are retained explicitly. The bilimit transfer instance belongs to the sibling
`FullSubbicategory.Bilimit` leaf.
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

variable {X Y Z : P.FullSubbicategory}
variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- Regard an ambient pseudopullback cone whose apex satisfies `P` as a cone in the full
subbicategory selected by `P`. All ambient `1`- and `2`-morphisms are retained. -/
@[stacks 02XQ "full-subbicategory lift of a pseudo-pullback cone"]
def inFull
    (S : PseudoPullbackCone f.hom g.hom) (hS : P S.pt) :
    PseudoPullbackCone f g where
  pt := ObjectProperty.FullSubbicategory.mk P S.pt hS
  fst := Bicategory.InducedBicategory.mkHom S.fst
  snd := Bicategory.InducedBicategory.mkHom S.snd
  iso := Bicategory.InducedBicategory.isoMk S.iso

/-- The ambient apex of a pseudopullback cone lifted to a full subbicategory is the original
ambient apex. -/
@[simp]
theorem inFull.pt.obj
    (S : PseudoPullbackCone f.hom g.hom) (hS : P S.pt) :
    (inFull P S hS).pt.1 = S.pt := sorry

/-- The ambient first projection of a pseudopullback cone lifted to a full subbicategory is
the original first projection. -/
@[simp]
theorem inFull.fst.hom
    (S : PseudoPullbackCone f.hom g.hom) (hS : P S.pt) :
    (inFull P S hS).fst.hom = S.fst := sorry

/-- The ambient second projection of a pseudopullback cone lifted to a full subbicategory is
the original second projection. -/
@[simp]
theorem inFull.snd.hom
    (S : PseudoPullbackCone f.hom g.hom) (hS : P S.pt) :
    (inFull P S hS).snd.hom = S.snd := sorry

/-- The comparison isomorphism of a pseudopullback cone lifted to a full subbicategory is the
ambient comparison isomorphism regarded in the induced hom category. -/
@[simp]
theorem inFull.iso
    (S : PseudoPullbackCone f.hom g.hom) (hS : P S.pt) :
    (inFull P S hS).iso = Bicategory.InducedBicategory.isoMk S.iso := sorry

/-- The ambient forward comparison cell of a pseudopullback cone lifted to a full
subbicategory is the original forward comparison cell. -/
@[simp]
theorem inFull.iso.hom
    (S : PseudoPullbackCone f.hom g.hom) (hS : P S.pt) :
    (inFull P S hS).iso.hom.hom = S.iso.hom := sorry

/-- The ambient inverse comparison cell of a pseudopullback cone lifted to a full
subbicategory is the original inverse comparison cell. -/
@[simp]
theorem inFull.iso.inv
    (S : PseudoPullbackCone f.hom g.hom) (hS : P S.pt) :
    (inFull P S hS).iso.inv.hom = S.iso.inv := sorry

/- Data and axiom audit (mathlib 4.32): `inFull` stores the ambient apex, projections, and
comparison isomorphism directly, adding only the supplied membership proof. Its non-`Prop`
data side introduces no choice; any deferred content is confined to the equality readouts. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
