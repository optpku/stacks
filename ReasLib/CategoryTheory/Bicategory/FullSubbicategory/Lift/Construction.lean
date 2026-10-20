/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict pseudofunctor lifts to full subbicategories

The generic lift is owned here because its only nontrivial input is an
objectwise membership proof.  The hom-wise local-equivalence facts for
property implications are isolated in a sibling module.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u' w' v'

namespace ObjectProperty

variable {D : Type u} [Bicategory.{w, v} D]

namespace FullSubbicategory

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {P : ObjectProperty D}

section

namespace Implementation

/-- The object, `1`-morphism, and `2`-morphism action of a strict pseudofunctor lifted to a
full subbicategory. -/
private def liftPrelaxStruct {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) :
    PrelaxFunctorStruct A P.FullSubbicategory where
  obj := fun X ↦ mk P (G.obj X) (obj_mem X)
  map := fun f ↦ Bicategory.InducedBicategory.mkHom (G.map f)
  map₂ := fun η ↦ Bicategory.InducedBicategory.mkHom₂ (G.map₂ η)

/-- The lifted action preserves identity `2`-morphisms. -/
private theorem liftMap₂Id {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    (liftPrelaxStruct G obj_mem).map₂ (𝟙 f) =
      𝟙 ((liftPrelaxStruct G obj_mem).map f) := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom₂_ext`; the underlying equality is
`G.map₂_id f`. -/

/-- The lifted action preserves vertical composition of `2`-morphisms. -/
private theorem liftMap₂Comp {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} {f g k : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ k) :
    (liftPrelaxStruct G obj_mem).map₂ (η ≫ θ) =
      (liftPrelaxStruct G obj_mem).map₂ η ≫
        (liftPrelaxStruct G obj_mem).map₂ θ := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom₂_ext`; the underlying equality is
`G.map₂_comp η θ`. -/

/-- The prelax functor underlying the lift to a full subbicategory. -/
private def liftPrelax {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) :
    PrelaxFunctor A P.FullSubbicategory where
  toPrelaxFunctorStruct := liftPrelaxStruct G obj_mem
  map₂_id := liftMap₂Id G obj_mem
  map₂_comp := liftMap₂Comp G obj_mem

/-- The lifted action preserves identity `1`-morphisms strictly. -/
private theorem liftMapId {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) (X : A) :
    (liftPrelax G obj_mem).map (𝟙 X) = 𝟙 ((liftPrelax G obj_mem).obj X) := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom_ext`; the underlying equality is
`G.map_id X`. -/

/-- The lifted action preserves horizontal composition strictly. -/
private theorem liftMapComp {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (liftPrelax G obj_mem).map (f ≫ g) =
      (liftPrelax G obj_mem).map f ≫ (liftPrelax G obj_mem).map g := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom_ext`; the underlying equality is
`G.map_comp f g`. -/

/-- The transport equality at the source of a lifted left unitor. -/
private theorem liftMapIdComp {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    (liftPrelax G obj_mem).map (𝟙 X ≫ f) =
      𝟙 ((liftPrelax G obj_mem).obj X) ≫ (liftPrelax G obj_mem).map f := sorry
/- Proof strategy: combine `liftMapComp G obj_mem (𝟙 X) f` with
`liftMapId G obj_mem X`. -/

/-- The transport equality at the source of a lifted right unitor. -/
private theorem liftMapCompId {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    (liftPrelax G obj_mem).map (f ≫ 𝟙 Y) =
      (liftPrelax G obj_mem).map f ≫ 𝟙 ((liftPrelax G obj_mem).obj Y) := sorry
/- Proof strategy: combine `liftMapComp G obj_mem f (𝟙 Y)` with
`liftMapId G obj_mem Y`. -/

/-- The left-associated transport equality for a lifted associator. -/
private theorem liftMapAssocLeft {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (k : Y ⟶ Z) :
    (liftPrelax G obj_mem).map ((f ≫ g) ≫ k) =
      ((liftPrelax G obj_mem).map f ≫ (liftPrelax G obj_mem).map g) ≫
        (liftPrelax G obj_mem).map k := sorry
/- Proof strategy: apply `liftMapComp` twice to the left-associated composite. -/

/-- The right-associated transport equality for a lifted associator. -/
private theorem liftMapAssocRight {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (k : Y ⟶ Z) :
    (liftPrelax G obj_mem).map f ≫
        ((liftPrelax G obj_mem).map g ≫ (liftPrelax G obj_mem).map k) =
      (liftPrelax G obj_mem).map (f ≫ (g ≫ k)) := sorry
/- Proof strategy: use the symmetric forms of `liftMapComp` twice. -/

/-- Left-whiskering coherence for the lift to a full subbicategory. -/
private theorem liftMap₂WhiskerLeft {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} (f : X ⟶ Y) {g g₁ : Y ⟶ Z} (η : g ⟶ g₁) :
    (liftPrelax G obj_mem).map₂ (f ◁ η) =
      eqToHom (liftMapComp G obj_mem f g) ≫
        (liftPrelax G obj_mem).map f ◁ (liftPrelax G obj_mem).map₂ η ≫
          eqToHom (liftMapComp G obj_mem f g₁).symm := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom₂_ext`, then use the corresponding
whiskering coherence of `G`. -/

/-- Right-whiskering coherence for the lift to a full subbicategory. -/
private theorem liftMap₂WhiskerRight {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y Z : A} {f f₁ : X ⟶ Y} (η : f ⟶ f₁) (g : Y ⟶ Z) :
    (liftPrelax G obj_mem).map₂ (η ▷ g) =
      eqToHom (liftMapComp G obj_mem f g) ≫
        (liftPrelax G obj_mem).map₂ η ▷ (liftPrelax G obj_mem).map g ≫
          eqToHom (liftMapComp G obj_mem f₁ g).symm := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom₂_ext`, then use the corresponding
whiskering coherence of `G`. -/

/-- Left-unitor coherence for the lift to a full subbicategory. -/
private theorem liftMap₂LeftUnitor {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    (liftPrelax G obj_mem).map₂ (λ_ f).hom =
      eqToHom (liftMapIdComp G obj_mem f) ≫
        (λ_ ((liftPrelax G obj_mem).map f)).hom := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom₂_ext`, then use the left-unitor
coherence of `G`. -/

/-- Right-unitor coherence for the lift to a full subbicategory. -/
private theorem liftMap₂RightUnitor {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {X Y : A} (f : X ⟶ Y) :
    (liftPrelax G obj_mem).map₂ (ρ_ f).hom =
      eqToHom (liftMapCompId G obj_mem f) ≫
        (ρ_ ((liftPrelax G obj_mem).map f)).hom := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom₂_ext`, then use the right-unitor
coherence of `G`. -/

/-- Associator coherence for the lift to a full subbicategory. -/
private theorem liftMap₂Associator {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X))
    {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (k : Y ⟶ Z) :
    (liftPrelax G obj_mem).map₂ (α_ f g k).hom =
      eqToHom (liftMapAssocLeft G obj_mem f g k) ≫
        (α_ ((liftPrelax G obj_mem).map f) ((liftPrelax G obj_mem).map g)
          ((liftPrelax G obj_mem).map k)).hom ≫
            eqToHom (liftMapAssocRight G obj_mem f g k) := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom₂_ext`, then use the associator
coherence of `G`. -/

/-- The strict-pseudofunctor core of the lift to a full subbicategory. -/
private def liftCore {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) :
    StrictPseudofunctorCore A P.FullSubbicategory where
  __ := liftPrelax G obj_mem
  map_id := liftMapId G obj_mem
  map_comp := liftMapComp G obj_mem
  map₂_whisker_left := liftMap₂WhiskerLeft G obj_mem
  map₂_whisker_right := liftMap₂WhiskerRight G obj_mem
  map₂_left_unitor := liftMap₂LeftUnitor G obj_mem
  map₂_right_unitor := liftMap₂RightUnitor G obj_mem
  map₂_associator := liftMap₂Associator G obj_mem

end Implementation

/-- Lift a strict pseudofunctor to the full subbicategory selected by `P` when every image
object satisfies `P`. The action on `1`- and `2`-morphisms is the ambient action of `G`;
only the object-membership witnesses are added.

The construction is the canonical factorization

```text
A  ───────── lift G obj_mem ─────────▶  P.FullSubbicategory
│                                             │
│ G                                           │ ι P
▼                                             ▼
D  ───────────────── 𝟭 D ──────────────────▶  D
```
-/
@[simps!]
def lift {A : Type u'} [Bicategory.{w', v'} A]
    (G : StrictPseudofunctor A D) (obj_mem : ∀ X : A, P (G.obj X)) :
    StrictPseudofunctor A P.FullSubbicategory :=
  StrictPseudofunctor.mk' (Implementation.liftCore G obj_mem)

/-- A strict pseudofunctor that sends objects satisfying `Q` to objects satisfying `P`
induces a strict pseudofunctor between the corresponding full subbicategories. The construction
restricts the source along `ι Q` and then reuses `lift` for the target property. -/
def map {A : Type u'} [Bicategory.{w', v'} A] {Q : ObjectProperty A}
    (F : StrictPseudofunctor A D) (hF : ∀ X : A, Q X → P (F.obj X)) :
    StrictPseudofunctor Q.FullSubbicategory P.FullSubbicategory :=
  lift ((ι Q).comp F) (fun X ↦ hF X.1 X.property)

/-- If `P ≤ Q`, the inclusion of the full subbicategory selected by `P` into the one selected by
`Q`. It acts identically on ambient `1`- and `2`-morphisms and only transports the object
property. -/
@[simps!]
def ιOfLE {Q : ObjectProperty D} (h : P ≤ Q) :
    StrictPseudofunctor P.FullSubbicategory Q.FullSubbicategory :=
  lift (P := Q) (ι P) (fun X ↦ h X.1 X.property)

end

end FullSubbicategory

end ObjectProperty

end CategoryTheory
