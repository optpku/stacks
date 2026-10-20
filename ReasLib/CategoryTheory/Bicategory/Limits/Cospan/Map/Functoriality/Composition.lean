module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Iso.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition functoriality for mapping bicategorical cospans

Mapping a cospan transformation by a composite pseudofunctor and mapping it successively have
definitionally equal vertex maps. Their generating comparison isomorphisms are related by the
coherence of pseudofunctor composition, so the canonical comparison is an isomorphism of cospan
transformations with identity vertex components.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u w' v' u' w'' v'' u''

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']
variable {B'' : Type u''} [Bicategory.{w'', v''} B'']
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

namespace Implementation

/-- Identity vertex cells satisfy the left generating naturality square comparing mapping by
a composite pseudofunctor with successive mapping. -/
private theorem compositionIso.leftNaturality
    (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    (Iso.refl (Q.map (P.map ψ.left))).hom ▷ Q.map (P.map f') ≫
        (map (map ψ P) Q).leftIso.hom =
      (map ψ (P.comp Q)).leftIso.hom ≫
        Q.map (P.map f) ◁
          (Iso.refl (Q.map (P.map ψ.base))).hom := sorry

/-- Identity vertex cells satisfy the right generating naturality square comparing mapping by
a composite pseudofunctor with successive mapping. -/
private theorem compositionIso.rightNaturality
    (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    (Iso.refl (Q.map (P.map ψ.right))).hom ▷ Q.map (P.map g') ≫
        (map (map ψ P) Q).rightIso.hom =
      (map ψ (P.comp Q)).rightIso.hom ≫
        Q.map (P.map g) ◁
          (Iso.refl (Q.map (P.map ψ.base))).hom := sorry

end Implementation

/-- Mapping a cospan transformation by a composite pseudofunctor is canonically isomorphic to
successive mapping, with identity isomorphisms at all three vertices. -/
@[stacks 0040 "composition comparison for mapping bicategorical cospan transformations"]
def mapCompositionIso
    (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    map ψ (P.comp Q) ≅ map (map ψ P) Q :=
  Hom.isoMk
    (Iso.refl (Q.map (P.map ψ.left)))
    (Iso.refl (Q.map (P.map ψ.right)))
    (Iso.refl (Q.map (P.map ψ.base)))
    (Implementation.compositionIso.leftNaturality ψ P Q)
    (Implementation.compositionIso.rightNaturality ψ P Q)

/-- The forward left component of `mapCompositionIso` is an identity `2`-morphism. -/
@[simp]
theorem mapCompositionIso.hom.left
    (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    Hom.left (mapCompositionIso ψ P Q).hom =
      𝟙 (Q.map (P.map ψ.left)) := sorry

/-- The forward right component of `mapCompositionIso` is an identity `2`-morphism. -/
@[simp]
theorem mapCompositionIso.hom.right
    (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    Hom.right (mapCompositionIso ψ P Q).hom =
      𝟙 (Q.map (P.map ψ.right)) := sorry

/-- The forward base component of `mapCompositionIso` is an identity `2`-morphism. -/
@[simp]
theorem mapCompositionIso.hom.base
    (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    Hom.base (mapCompositionIso ψ P Q).hom =
      𝟙 (Q.map (P.map ψ.base)) := sorry

/-- The inverse left component of `mapCompositionIso` is an identity `2`-morphism. -/
@[simp]
theorem mapCompositionIso.inv.left
    (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    Hom.left (mapCompositionIso ψ P Q).inv =
      𝟙 (Q.map (P.map ψ.left)) := sorry

/-- The inverse right component of `mapCompositionIso` is an identity `2`-morphism. -/
@[simp]
theorem mapCompositionIso.inv.right
    (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    Hom.right (mapCompositionIso ψ P Q).inv =
      𝟙 (Q.map (P.map ψ.right)) := sorry

/-- The inverse base component of `mapCompositionIso` is an identity `2`-morphism. -/
@[simp]
theorem mapCompositionIso.inv.base
    (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') :
    Hom.base (mapCompositionIso ψ P Q).inv =
      𝟙 (Q.map (P.map ψ.base)) := sorry

/- Data and axiom audit (mathlib 4.32):

All three non-`Prop` components of `mapCompositionIso` are explicit reflexivity
isomorphisms on the definitionally equal composite vertex maps. Any `sorryAx` dependency is
confined to the two generating naturality squares and inherited modification-isomorphism laws. -/

end CategoryTheory.Bicategory.CospanTransform
