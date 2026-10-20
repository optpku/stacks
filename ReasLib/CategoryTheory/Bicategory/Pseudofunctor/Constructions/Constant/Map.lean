/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Constant.Basic

/-!
# Mapping constant pseudofunctors

The canonical comparison between a mapped constant diagram and the constant
diagram at the mapped object.
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

universe wC vC uC

variable {C : Type uC} [Bicategory.{wC, vC} C]

section MapConstImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The identity components of the canonical comparison from the constant diagram at `K.obj X`
to the image under `K` of the constant diagram at `X`. -/
private def mapConst.app (K : B ⥤ᵖ C) (X : B) (a : J) :
    (const J (K.obj X)).obj a ⟶ ((const J X).comp K).obj a :=
  𝟙 (K.obj X)

/-- The naturality isomorphism of the canonical comparison from `const J (K.obj X)` to
`(const J X).comp K`. Its nontrivial factor is the inverse identity comparison of `K`. -/
private def mapConst.naturality (K : B ⥤ᵖ C) (X : B)
    {a b : J} (f : a ⟶ b) :
    (const J (K.obj X)).map f ≫ mapConst.app K X b ≅
      mapConst.app K X a ≫ ((const J X).comp K).map f :=
  λ_ (𝟙 (K.obj X)) ≪≫ (K.mapId X).symm ≪≫
    (λ_ (K.map (𝟙 X))).symm

/-- Naturality in `2`-morphisms for the comparison between a mapped constant diagram and the
constant diagram at the mapped object. -/
private theorem mapConst.naturality.map₂ (K : B ⥤ᵖ C) (X : B) :
    ∀ {a b : J} {f g : a ⟶ b} (θ : f ⟶ g),
      (const J (K.obj X)).map₂ θ ▷ mapConst.app K X b ≫
          (mapConst.naturality K X g).hom =
        (mapConst.naturality K X f).hom ≫
          mapConst.app K X a ◁ ((const J X).comp K).map₂ θ := sorry
/- Proof strategy: unfold both constant pseudofunctors. Their mapped `2`-cells are identities;
the remaining equation follows from naturality of `K.mapId X` and the unitors. -/

/-- Identity coherence for the comparison between a mapped constant diagram and the constant
diagram at the mapped object. -/
private theorem mapConst.naturality.mapId (K : B ⥤ᵖ C) (X : B) :
    ∀ a : J,
      (mapConst.naturality K X (𝟙 a)).hom ≫
          mapConst.app K X a ◁ (((const J X).comp K).mapId a).hom =
        ((const J (K.obj X)).mapId a).hom ▷ mapConst.app K X a ≫
          (λ_ (mapConst.app K X a)).hom ≫
          (ρ_ (mapConst.app K X a)).inv := sorry
/- Proof strategy: expand the two `mapId` constraints and use the pseudofunctor identity
coherence of `K`; all remaining arrows are identities and normalize by unitor coherence. -/

/-- Composition coherence for the comparison between a mapped constant diagram and the constant
diagram at the mapped object. -/
private theorem mapConst.naturality.mapComp (K : B ⥤ᵖ C) (X : B) :
    ∀ {a b c : J} (f : a ⟶ b) (g : b ⟶ c),
      (mapConst.naturality K X (f ≫ g)).hom ≫
          mapConst.app K X a ◁ (((const J X).comp K).mapComp f g).hom =
        ((const J (K.obj X)).mapComp f g).hom ▷ mapConst.app K X c ≫
          (α_ _ _ _).hom ≫
          (const J (K.obj X)).map f ◁ (mapConst.naturality K X g).hom ≫
          (α_ _ _ _).inv ≫
          (mapConst.naturality K X f).hom ▷ ((const J X).comp K).map g ≫
          (α_ _ _ _).hom := sorry
/- Proof strategy: unfold the constant `mapComp` constraints, expand the composite-pseudofunctor
constraint, and reduce the resulting pasting to the `mapComp` identity laws and
associator/unitor coherence of `K`. -/

end Implementation

variable (J) in
/-- The canonical strong comparison from the constant diagram at `K.obj X` to the image under
`K` of the constant diagram at `X`.

This is the shape-independent comparison needed when a pseudofunctor maps a conical pseudocone.
It belongs to the pseudofunctor construction layer: neither limits nor a particular diagram
shape occur in its definition. -/
def mapConst (K : B ⥤ᵖ C) (X : B) :
    StrongTrans (const J (K.obj X)) ((const J X).comp K) where
  app := Implementation.mapConst.app K X
  naturality := Implementation.mapConst.naturality K X
  naturality_naturality := Implementation.mapConst.naturality.map₂ K X
  naturality_id := Implementation.mapConst.naturality.mapId K X
  naturality_comp := Implementation.mapConst.naturality.mapComp K X

/-- Every component of the comparison from the constant diagram at `K.obj X` to the mapped
constant diagram is an identity `1`-morphism. -/
@[simp]
theorem mapConst.app (K : B ⥤ᵖ C) (X : B) (a : J) :
    (mapConst J K X).app a = 𝟙 (K.obj X) := sorry
/- Proof strategy: unfold `mapConst` and its stored component. -/

/-- The naturality comparison of `mapConst` is obtained from the inverse identity comparison of
`K`, with the two required unitors. -/
@[simp]
theorem mapConst.naturality (K : B ⥤ᵖ C) (X : B)
    {a b : J} (f : a ⟶ b) :
    (mapConst J K X).naturality f =
      λ_ (𝟙 (K.obj X)) ≪≫ (K.mapId X).symm ≪≫
        (λ_ (K.map (𝟙 X))).symm := sorry
/- Proof strategy: unfold `mapConst` and read its explicitly stored naturality isomorphism. -/

/- Data audit (mathlib 4.32): `mapConst` stores every object component and naturality
isomorphism explicitly. Its `#print axioms` report contains `sorryAx` only through the three
proof-valued strong-transformation coherence fields and coherence inherited from `const`; no
object, `1`-morphism, `2`-morphism, or isomorphism datum is selected by a proof witness. -/

end MapConstImplementation

end Pseudofunctor

end CategoryTheory
