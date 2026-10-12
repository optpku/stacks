/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Constant.StrongTrans

/-!
# The varying constant-diagram pseudofunctor

The pseudofunctor from a bicategory into its bicategory of constant diagrams,
together with its object, morphism, cell, and comparison computations.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

universe wJ vJ uJ

variable {B : Type u} [Bicategory.{w, v} B]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

section ConstantDiagramImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Naturality of the identity comparison for the varying constant diagram construction. -/
private theorem constDiagram.mapId.naturality (X : B) :
    ∀ {a b : J} (h : a ⟶ b),
      (const J X).map h ◁ (Iso.refl (𝟙 X)).hom ≫
        ((Pseudofunctor.StrongTrans.id (const J X)).naturality h).hom =
        ((constMap J (𝟙 X)).naturality h).hom ≫
          (Iso.refl (𝟙 X)).hom ▷ (const J X).map h := sorry
/- Proof strategy: unfold `constMap` and normalize the identity transformation unitors by
bicategory coherence. -/

/-- The implementation-level identity comparison for varying constant diagrams. -/
private def constDiagram.mapId.iso (X : B) :
    constMap J (𝟙 X) ≅ 𝟙 (const J X) :=
  StrongTrans.isoMk (fun _ ↦ Iso.refl _) (constDiagram.mapId.naturality X)

/-- Naturality of the composition comparison for the varying constant diagram construction. -/
private theorem constDiagram.mapComp.naturality {X Y Z : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ {a b : J} (h : a ⟶ b),
      (const J X).map h ◁ (Iso.refl (f ≫ g)).hom ≫
        ((constMap J f ≫ constMap J g).naturality h).hom =
        ((constMap J (f ≫ g)).naturality h).hom ≫
          (Iso.refl (f ≫ g)).hom ▷ (const J Z).map h := sorry
/- Proof strategy: unfold strong-transformation composition and `constMap`; componentwise
both sides are `f ≫ g`, and the rest is bicategory coherence. -/

/-- The implementation-level composition comparison for varying constant diagrams. -/
private def constDiagram.mapComp.iso {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    constMap J (f ≫ g) ≅ constMap J f ≫ constMap J g :=
  StrongTrans.isoMk (fun _ ↦ Iso.refl _) (constDiagram.mapComp.naturality f g)

/-- The implementation-level prelax core for varying constant diagrams. -/
private def constDiagram.prelax
    (J : Type uJ) [Bicategory.{wJ, vJ} J]
    (B : Type u) [Bicategory.{w, v} B] : PrelaxFunctor B (J ⥤ᵖ B) :=
  PrelaxFunctor.mkOfHomFunctors (fun X ↦ const J X) fun X Y ↦
    constMapFunctor J X Y

/-- Varying constant diagrams preserve left whiskering. -/
private theorem constDiagram.map₂.whiskerLeft
    (J : Type uJ) [Bicategory.{wJ, vJ} J]
    (B : Type u) [Bicategory.{w, v} B] :
    ∀ {X Y Z : B} (f : X ⟶ Y) {g h : Y ⟶ Z} (η : g ⟶ h),
      (constDiagram.prelax J B).map₂ (f ◁ η) =
        (constDiagram.mapComp.iso f g).hom ≫
          (constDiagram.prelax J B).map f ◁ (constDiagram.prelax J B).map₂ η ≫
          (constDiagram.mapComp.iso f h).inv := sorry
/- Proof strategy: evaluate modifications componentwise, unfold `constMap₂`, and use the
ambient left-whiskering law. -/

/-- Varying constant diagrams preserve right whiskering. -/
private theorem constDiagram.map₂.whiskerRight
    (J : Type uJ) [Bicategory.{wJ, vJ} J]
    (B : Type u) [Bicategory.{w, v} B] :
    ∀ {X Y Z : B} {f g : X ⟶ Y} (η : f ⟶ g) (h : Y ⟶ Z),
      (constDiagram.prelax J B).map₂ (η ▷ h) =
        (constDiagram.mapComp.iso f h).hom ≫
          (constDiagram.prelax J B).map₂ η ▷ (constDiagram.prelax J B).map h ≫
          (constDiagram.mapComp.iso g h).inv := sorry
/- Proof strategy: evaluate modifications componentwise, unfold `constMap₂`, and use the
ambient right-whiskering law. -/

/-- Varying constant diagrams preserve the associator. -/
private theorem constDiagram.map₂.associator
    (J : Type uJ) [Bicategory.{wJ, vJ} J]
    (B : Type u) [Bicategory.{w, v} B] :
    ∀ {W X Y Z : B} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
      (constDiagram.prelax J B).map₂ (α_ f g h).hom =
        (constDiagram.mapComp.iso (f ≫ g) h).hom ≫
          (constDiagram.mapComp.iso f g).hom ▷ (constDiagram.prelax J B).map h ≫
          (α_ ((constDiagram.prelax J B).map f) ((constDiagram.prelax J B).map g)
            ((constDiagram.prelax J B).map h)).hom ≫
          (constDiagram.prelax J B).map f ◁ (constDiagram.mapComp.iso g h).inv ≫
          (constDiagram.mapComp.iso f (g ≫ h)).inv := sorry
/- Proof strategy: evaluate modifications at each object of `J`; comparison components are
identities, leaving ambient associator coherence. -/

/-- Varying constant diagrams preserve the left unitor. -/
private theorem constDiagram.map₂.leftUnitor
    (J : Type uJ) [Bicategory.{wJ, vJ} J]
    (B : Type u) [Bicategory.{w, v} B] :
    ∀ {X Y : B} (f : X ⟶ Y),
      (constDiagram.prelax J B).map₂ (λ_ f).hom =
        (constDiagram.mapComp.iso (𝟙 X) f).hom ≫
          (constDiagram.mapId.iso X).hom ▷ (constDiagram.prelax J B).map f ≫
          (λ_ ((constDiagram.prelax J B).map f)).hom := sorry
/- Proof strategy: evaluate componentwise and reduce to the ambient triangle coherence for the
identity comparison and left unitor. -/

/-- Varying constant diagrams preserve the right unitor. -/
private theorem constDiagram.map₂.rightUnitor
    (J : Type uJ) [Bicategory.{wJ, vJ} J]
    (B : Type u) [Bicategory.{w, v} B] :
    ∀ {X Y : B} (f : X ⟶ Y),
      (constDiagram.prelax J B).map₂ (ρ_ f).hom =
        (constDiagram.mapComp.iso f (𝟙 Y)).hom ≫
          (constDiagram.prelax J B).map f ◁ (constDiagram.mapId.iso Y).hom ≫
          (ρ_ ((constDiagram.prelax J B).map f)).hom := sorry
/- Proof strategy: evaluate componentwise and reduce to the ambient triangle coherence for the
identity comparison and right unitor. -/

end Implementation

/-- The pseudofunctor sending `X : B` to the constant `J`-shaped diagram at `X` and acting
pointwise on `1`- and `2`-morphisms. This is the shape-independent owner for varying-apex
conical pseudocones. -/
def constDiagram (J : Type uJ) [Bicategory.{wJ, vJ} J]
    (B : Type u) [Bicategory.{w, v} B] : B ⥤ᵖ (J ⥤ᵖ B) where
  toPrelaxFunctor := Implementation.constDiagram.prelax J B
  mapId := Implementation.constDiagram.mapId.iso
  mapComp := Implementation.constDiagram.mapComp.iso
  map₂_whisker_left := Implementation.constDiagram.map₂.whiskerLeft J B
  map₂_whisker_right := Implementation.constDiagram.map₂.whiskerRight J B
  map₂_associator := Implementation.constDiagram.map₂.associator J B
  map₂_left_unitor := Implementation.constDiagram.map₂.leftUnitor J B
  map₂_right_unitor := Implementation.constDiagram.map₂.rightUnitor J B

variable (J) in
/-- The object action of the varying constant-diagram pseudofunctor is `const`. -/
@[simp]
theorem constDiagram.obj (X : B) :
    (constDiagram J B).obj X = const J X := sorry

variable (J) in
/-- The `1`-morphism action of the varying constant-diagram pseudofunctor is `constMap`. -/
@[simp]
theorem constDiagram.map {X Y : B} (f : X ⟶ Y) :
    (constDiagram J B).map f = constMap J f := sorry

variable (J) in
/-- The `2`-morphism action of the varying constant-diagram pseudofunctor is `constMap₂`. -/
@[simp]
theorem constDiagram.map₂ {X Y : B} {f g : X ⟶ Y} (η : f ⟶ g) :
    (constDiagram J B).map₂ η = constMap₂ J η := sorry

variable (J) in
/-- The hom functor of the varying constant-diagram pseudofunctor is `constMapFunctor`. -/
@[simp]
theorem constDiagram.mapFunctor (X Y : B) :
    (constDiagram J B).mapFunctor X Y = constMapFunctor J X Y := sorry

/-- The forward component of the identity comparison for varying constant diagrams is an
identity `2`-morphism. -/
@[simp]
theorem constDiagram.mapId.hom.app (X : B) (a : J) :
    ((constDiagram J B).mapId X).hom.as.app a = 𝟙 (𝟙 X) := sorry

/-- The inverse component of the identity comparison for varying constant diagrams is an
identity `2`-morphism. -/
@[simp]
theorem constDiagram.mapId.inv.app (X : B) (a : J) :
    ((constDiagram J B).mapId X).inv.as.app a = 𝟙 (𝟙 X) := sorry

/-- The forward component of the composition comparison for varying constant diagrams is an
identity `2`-morphism. -/
@[simp]
theorem constDiagram.mapComp.hom.app {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (a : J) :
    ((constDiagram J B).mapComp f g).hom.as.app a = 𝟙 (f ≫ g) := sorry

/-- The inverse component of the composition comparison for varying constant diagrams is an
identity `2`-morphism. -/
@[simp]
theorem constDiagram.mapComp.inv.app {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (a : J) :
    ((constDiagram J B).mapComp f g).inv.as.app a = 𝟙 (f ≫ g) := sorry

end ConstantDiagramImplementation

end Pseudofunctor

end CategoryTheory
