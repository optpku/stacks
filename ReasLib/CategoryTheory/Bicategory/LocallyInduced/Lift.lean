/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Morphisms
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory

/-!
# Inclusions and lifts for locally induced bicategories

The canonical inclusion forgets hom-property witnesses. A strict pseudofunctor into the ambient
induced bicategory lifts precisely when all of its mapped `1`-morphisms satisfy the selected
hom property. Local full faithfulness of the canonical inclusions is recorded separately in
`LocallyInduced.Factorization`.
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

section InclusionAndLift

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {A : Type u''} [Bicategory.{w', v'} A]

variable (C F Q) in
/-- The canonical locally full inclusion into the induced bicategory with the same objects and
all ambient `1`-morphisms. It forgets only the hom-property witnesses.

The ambient bicategory, object map, and hom property are explicit because this strict
pseudofunctor has no value input from which Lean can recover them. -/
@[stacks 0040 "canonical inclusion of a locally induced bicategory", simps!]
def ι : StrictPseudofunctor (LocallyInducedBicategory C F Q) (InducedBicategory C F) :=
  StrictPseudofunctor.mk' {
    obj := fun X ↦ X
    map := fun f ↦ InducedBicategory.mkHom f.obj
    map₂ := fun η ↦ InducedBicategory.mkHom₂ η.hom }

namespace Implementation.Lift

/-- The generic lift preserves identity `2`-morphisms. -/
private theorem map₂Id (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} (f : X ⟶ Y) :
    mkHom₂ (G.map₂ (𝟙 f)).hom =
      𝟙 (mkHom (G.map f).hom (map_mem f)) := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext` and project `G.map₂_id f` to the ambient
`2`-morphism. -/

/-- The generic lift preserves vertical composition of `2`-morphisms. -/
private theorem map₂Comp (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} {f g k : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ k) :
    mkHom₂ (G.map₂ (η ≫ θ)).hom =
      (mkHom₂ (G.map₂ η).hom :
        mkHom (G.map f).hom (map_mem f) ⟶ mkHom (G.map g).hom (map_mem g)) ≫
        (mkHom₂ (G.map₂ θ).hom :
          mkHom (G.map g).hom (map_mem g) ⟶ mkHom (G.map k).hom (map_mem k)) := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext` and project `G.map₂_comp η θ` to the ambient
`2`-morphism. -/

/-- The generic lift preserves identity `1`-morphisms strictly. -/
private theorem mapId (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom) (X : A) :
    mkHom (G.map (𝟙 X)).hom (map_mem (𝟙 X)) =
      mkHom (𝟙 (F (G.obj X))) (Q.id_mem (G.obj X)) := sorry
/- Proof strategy: apply `ObjectProperty.FullSubcategory.ext`; obtain the ambient equality by
applying `congrArg InducedBicategory.Hom.hom` to `G.map_id X`. -/

/-- The generic lift preserves horizontal composition strictly. -/
private theorem mapComp (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mkHom (G.map (f ≫ g)).hom (map_mem (f ≫ g)) =
      mkHom (G.map f).hom (map_mem f) ≫ mkHom (G.map g).hom (map_mem g) := sorry
/- Proof strategy: apply `ObjectProperty.FullSubcategory.ext`; obtain the ambient equality by
applying `congrArg InducedBicategory.Hom.hom` to `G.map_comp f g`. -/

/-- The transport equality at the source of a lifted left unitor. -/
private theorem mapIdComp (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} (f : X ⟶ Y) :
    mkHom (G.map (𝟙 X ≫ f)).hom (map_mem (𝟙 X ≫ f)) =
      mkHom (𝟙 (F (G.obj X))) (Q.id_mem (G.obj X)) ≫
        mkHom (G.map f).hom (map_mem f) := sorry
/- Proof strategy: combine `mapComp G map_mem (𝟙 X) f` with `mapId G map_mem X`. -/

/-- The transport equality at the source of a lifted right unitor. -/
private theorem mapCompId (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} (f : X ⟶ Y) :
    mkHom (G.map (f ≫ 𝟙 Y)).hom (map_mem (f ≫ 𝟙 Y)) =
      mkHom (G.map f).hom (map_mem f) ≫
        mkHom (𝟙 (F (G.obj Y))) (Q.id_mem (G.obj Y)) := sorry
/- Proof strategy: combine `mapComp G map_mem f (𝟙 Y)` with `mapId G map_mem Y`. -/

/-- Left-unitor coherence for the generic lift. -/
private theorem map₂LeftUnitor (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} (f : X ⟶ Y) :
    mkHom₂ (G.map₂ (λ_ f).hom).hom =
      eqToHom (mapIdComp G map_mem f) ≫
        (λ_ (mkHom (G.map f).hom (map_mem f))).hom := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`, project the left-unitor coherence of `G`,
and use the named identity/composition transport. -/

/-- Right-unitor coherence for the generic lift. -/
private theorem map₂RightUnitor (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} (f : X ⟶ Y) :
    mkHom₂ (G.map₂ (ρ_ f).hom).hom =
      eqToHom (mapCompId G map_mem f) ≫
        (ρ_ (mkHom (G.map f).hom (map_mem f))).hom := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`, project the right-unitor coherence of `G`,
and use the named composition/identity transport. -/

/-- The left-associated transport equality needed by the lifted associator. -/
private theorem mapAssocLeft (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (k : Y ⟶ Z) :
    mkHom (G.map ((f ≫ g) ≫ k)).hom (map_mem ((f ≫ g) ≫ k)) =
      (mkHom (G.map f).hom (map_mem f) ≫ mkHom (G.map g).hom (map_mem g)) ≫
        mkHom (G.map k).hom (map_mem k) := sorry
/- Proof strategy: apply `mapComp` first to `(f ≫ g, k)` and then to `(f, g)`, transporting
only the Prop-valued membership witnesses by full-subcategory extensionality. -/

/-- The right-associated transport equality needed by the lifted associator. -/
private theorem mapAssocRight (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (k : Y ⟶ Z) :
    mkHom (G.map f).hom (map_mem f) ≫
        (mkHom (G.map g).hom (map_mem g) ≫ mkHom (G.map k).hom (map_mem k)) =
      mkHom (G.map (f ≫ (g ≫ k))).hom (map_mem (f ≫ (g ≫ k))) := sorry
/- Proof strategy: use the symmetric forms of `mapComp` first for `(g, k)` and then for
`(f, g ≫ k)`, again discarding only proof-field differences by extensionality. -/

/-- Left-whiskering coherence for the generic lift. -/
private theorem map₂WhiskerLeft (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y Z : A} (f : X ⟶ Y) {g g₁ : Y ⟶ Z} (η : g ⟶ g₁) :
    mkHom₂ (G.map₂ (f ◁ η)).hom =
      eqToHom (mapComp G map_mem f g) ≫
        mkHom (G.map f).hom (map_mem f) ◁
          (mkHom₂ (G.map₂ η).hom :
            mkHom (G.map g).hom (map_mem g) ⟶
              mkHom (G.map g₁).hom (map_mem g₁)) ≫
            eqToHom (mapComp G map_mem f g₁).symm := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; project the left-whiskering coherence of `G`
through `InducedBicategory.Hom₂.hom`, then remove the equality transports with the induced and
full-subcategory `eqToHom` projection lemmas. -/

/-- Right-whiskering coherence for the generic lift. -/
private theorem map₂WhiskerRight (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y Z : A} {f f₁ : X ⟶ Y} (η : f ⟶ f₁) (g : Y ⟶ Z) :
    mkHom₂ (G.map₂ (η ▷ g)).hom =
      eqToHom (mapComp G map_mem f g) ≫
        (mkHom₂ (G.map₂ η).hom :
          mkHom (G.map f).hom (map_mem f) ⟶
            mkHom (G.map f₁).hom (map_mem f₁)) ▷
          mkHom (G.map g).hom (map_mem g) ≫
            eqToHom (mapComp G map_mem f₁ g).symm := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; project the right-whiskering coherence of `G`
through `InducedBicategory.Hom₂.hom`, then remove the equality transports with the induced and
full-subcategory `eqToHom` projection lemmas. -/

/-- Associator coherence for the generic lift. -/
private theorem map₂Associator (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (k : Y ⟶ Z) :
    mkHom₂ (G.map₂ (α_ f g k).hom).hom =
      eqToHom (mapAssocLeft G map_mem f g k) ≫
        (α_ (mkHom (G.map f).hom (map_mem f))
          (mkHom (G.map g).hom (map_mem g))
          (mkHom (G.map k).hom (map_mem k))).hom ≫
            eqToHom (mapAssocRight G map_mem f g k) := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; project the associator coherence of `G`
through `InducedBicategory.Hom₂.hom`, use `associator_hom`, and identify both named transport
equalities with the projected strict-composition transports of `G`. -/

end Implementation.Lift

/-- Lift a strict pseudofunctor into a locally induced bicategory when each mapped
`1`-morphism satisfies the target hom property. The object and `2`-morphism actions are inherited
from `G`; only the Prop-valued hom-membership witnesses are added.

The lift gives the canonical factorization
```text
A  ───────── lift G map_mem ─────────▶  LocallyInducedBicategory C F Q
│ G                                             │ ι
▼                                               ▼
InducedBicategory C F  ───────── 𝟙 ─────────▶  InducedBicategory C F
```
whose square commutes on objects, `1`-morphisms, and `2`-morphisms. -/
@[stacks 0040 "strict pseudofunctor lift through a hom property", simps!]
def lift (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom) :
    StrictPseudofunctor A (LocallyInducedBicategory C F Q) :=
  StrictPseudofunctor.mk' {
    obj := G.obj
    map := fun f ↦ mkHom (G.map f).hom (map_mem f)
    map₂ := fun η ↦ mkHom₂ (G.map₂ η).hom
    map₂_id := Implementation.Lift.map₂Id G map_mem
    map₂_comp := Implementation.Lift.map₂Comp G map_mem
    map_id := Implementation.Lift.mapId G map_mem
    map_comp := Implementation.Lift.mapComp G map_mem
    map₂_whisker_left := Implementation.Lift.map₂WhiskerLeft G map_mem
    map₂_whisker_right := Implementation.Lift.map₂WhiskerRight G map_mem
    map₂_left_unitor := Implementation.Lift.map₂LeftUnitor G map_mem
    map₂_right_unitor := Implementation.Lift.map₂RightUnitor G map_mem
    map₂_associator := Implementation.Lift.map₂Associator G map_mem }

variable {R : HomProperty F} [R.IsMultiplicative]

/-- The canonical inclusion induced by an implication between hom properties. -/
@[stacks 0040 "inclusion induced by an implication of hom properties", simps!]
def ιOfLE (h : Q ≤ R) :
    StrictPseudofunctor (LocallyInducedBicategory C F Q)
      (LocallyInducedBicategory C F R) :=
  lift (Q := R) (ι C F Q) (fun f ↦ h _ _ f.obj f.property)

variable (C F Q) in
/-- The canonical inclusion into the ambient bicategory is the composite
```text
LocallyInducedBicategory C F Q  ───── ι ─────▶  InducedBicategory C F
  ───── InducedBicategory.forget ─────▶  C.
```
Thus the first map forgets hom-property witnesses and the second forgets the induced-object
presentation. The ambient bicategory, object map, and hom property are explicit because this
strict pseudofunctor has no value input from which Lean can recover them. -/
@[stacks 0040 "ambient forgetful map of a locally induced bicategory", simps!]
def forget : StrictPseudofunctor (LocallyInducedBicategory C F Q) C :=
  (ι C F Q).comp InducedBicategory.forget

end InclusionAndLift

/- Data audit (mathlib 4.32): `ι`, `lift`, `ιOfLE`, and `forget` copy
ambient object, `1`-morphism, and `2`-morphism data explicitly. Deferred
content is confined to strict-pseudofunctor laws and coherence fields. -/

end LocallyInducedBicategory

end Bicategory

end CategoryTheory
