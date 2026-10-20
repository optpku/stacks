/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory

/-!
# Pseudofunctor lifts to locally induced bicategories

This file owns the arbitrary pseudofunctor lift into a locally induced
bicategory.  The computation lemmas are separated into
`LocallyInduced.Pseudofunctor.Computations`.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u' w' v' u''

namespace Bicategory

variable {B : Type u'}

namespace LocallyInducedBicategory

variable {C : Type u} [Bicategory.{w, v} C] {F : B → C}
  {Q : HomProperty F} [Q.IsMultiplicative]

section PseudofunctorLift

variable {A : Type u''} [Bicategory.{w', v'} A]

/-- Lift a pseudofunctor into a locally induced bicategory when every mapped
1-morphism satisfies the selected hom property.

The lifted pseudofunctor retains the object, 1-morphism, 2-morphism,
identity-comparison, and composition-comparison data of G; only
Prop-valued hom-membership witnesses are added. -/
@[stacks 0040 "lift a pseudofunctor through a hom property"]
def liftPseudofunctor (G : Pseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom) :
    Pseudofunctor A (LocallyInducedBicategory C F Q) where
  obj := G.obj
  map := fun f ↦ mkHom (G.map f).hom (map_mem f)
  map₂ := fun η ↦ mkHom₂ (G.map₂ η).hom
  map₂_id := sorry
  map₂_comp := sorry
  mapId := fun X ↦ isoMk (InducedBicategory.Iso.toAmbient (G.mapId X))
  mapComp := fun f g ↦ isoMk (InducedBicategory.Iso.toAmbient (G.mapComp f g))
  map₂_whisker_left := sorry
  map₂_whisker_right := sorry
  map₂_associator := sorry
  map₂_left_unitor := sorry
  map₂_right_unitor := sorry

end PseudofunctorLift

/- Data audit (mathlib 4.32): `liftPseudofunctor` copies all object, map,
`2`-morphism, identity-comparison, and composition-comparison data from `G`.
The only deferred fields are category laws and coherence propositions; the
hom-property witnesses themselves are explicit inputs. -/

end LocallyInducedBicategory

end Bicategory

end CategoryTheory
