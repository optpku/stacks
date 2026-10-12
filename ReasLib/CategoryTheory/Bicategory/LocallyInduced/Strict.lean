/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# Strict locally induced bicategories

Strictness of an ambient bicategory is inherited by its locally induced bicategory. The proof
uses the ambient representative computations from the basic construction.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u'

namespace Bicategory

variable {B : Type u'}

namespace LocallyInducedBicategory

variable {C : Type u} [Bicategory.{w, v} C] {F : B → C}
  {Q : HomProperty F} [Q.IsMultiplicative]

section Strict

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable [Strict C]

namespace Implementation

/-- Left composition by the identity is strictly unital in the locally induced bicategory. -/
private theorem strictIdComp {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    𝟙 X ≫ f = f := sorry
/- Proof strategy: apply `ObjectProperty.FullSubcategory.ext`, then use
`Strict.id_comp f.obj` in the ambient strict bicategory. -/

/-- Right composition by the identity is strictly unital in the locally induced bicategory. -/
private theorem strictCompId {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    f ≫ 𝟙 Y = f := sorry
/- Proof strategy: apply `ObjectProperty.FullSubcategory.ext`, then use
`Strict.comp_id f.obj` in the ambient strict bicategory. -/

/-- Composition is strictly associative in the locally induced bicategory. -/
private theorem strictAssoc {W X Y Z : LocallyInducedBicategory C F Q}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := sorry
/- Proof strategy: apply `ObjectProperty.FullSubcategory.ext`, then use
`Strict.assoc f.obj g.obj h.obj` in the ambient strict bicategory. -/

/-- The inherited left unitor is the equality isomorphism induced by strict left unitality. -/
private theorem strictLeftUnitorEqToIso {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    λ_ f = eqToIso (strictIdComp f) := sorry
/- Proof strategy: use `Iso.ext` and `ObjectProperty.hom_ext`, rewrite by
`leftUnitor_hom` and the ambient `Strict.leftUnitor_eqToIso`, and compare the underlying
equality morphisms with `ObjectProperty.eqToHom_hom`. -/

/-- The inherited right unitor is the equality isomorphism induced by strict right unitality. -/
private theorem strictRightUnitorEqToIso {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    ρ_ f = eqToIso (strictCompId f) := sorry
/- Proof strategy: use `Iso.ext` and `ObjectProperty.hom_ext`, rewrite by
`rightUnitor_hom` and the ambient `Strict.rightUnitor_eqToIso`, and compare the underlying
equality morphisms with `ObjectProperty.eqToHom_hom`. -/

/-- The inherited associator is the equality isomorphism induced by strict associativity. -/
private theorem strictAssociatorEqToIso {V W X Y : LocallyInducedBicategory C F Q}
    (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y) :
    α_ f g h = eqToIso (strictAssoc f g h) := sorry
/- Proof strategy: use `Iso.ext` and `ObjectProperty.hom_ext`, rewrite by
`associator_hom` and the ambient `Strict.associator_eqToIso`, and compare the underlying
equality morphisms with `ObjectProperty.eqToHom_hom`. -/

end Implementation

/-- An induced locally full bicategory in a strict bicategory is strict. -/
@[stacks 0040 "strictness of a locally induced bicategory"]
instance strict : Strict (LocallyInducedBicategory C F Q) where
  id_comp := Implementation.strictIdComp
  comp_id := Implementation.strictCompId
  assoc := Implementation.strictAssoc
  leftUnitor_eqToIso := Implementation.strictLeftUnitorEqToIso
  rightUnitor_eqToIso := Implementation.strictRightUnitorEqToIso
  associator_eqToIso := Implementation.strictAssociatorEqToIso

end Strict

end LocallyInducedBicategory

end Bicategory

end CategoryTheory
