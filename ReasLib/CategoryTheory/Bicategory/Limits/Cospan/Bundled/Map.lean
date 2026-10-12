/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Projection

/-!
# Computations for mapping bundled bicategorical cospans

This file is the projection-level API for `Cospan.map`. The namespaces `map.obj`, `map.hom`,
and `map.map₂` identify its bundled object, `1`-morphism, and `2`-morphism actions with the
canonical componentwise operations from the walking-cospan layer. They expose the five object
fields, five `1`-morphism generators, and three `2`-morphism components.

Identity and composition comparisons are intentionally kept in a separate coherence layer.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']

/-- Mapping a bundled cospan applies the ambient pseudofunctor to its left endpoint. -/
@[simp]
theorem map.obj.left (P : B ⥤ᵖ B') (S : Cospan B) :
    ((map P).obj S).left = P.obj S.left := sorry

/-- Mapping a bundled cospan applies the ambient pseudofunctor to its right endpoint. -/
@[simp]
theorem map.obj.right (P : B ⥤ᵖ B') (S : Cospan B) :
    ((map P).obj S).right = P.obj S.right := sorry

/-- Mapping a bundled cospan applies the ambient pseudofunctor to its common target. -/
@[simp]
theorem map.obj.base (P : B ⥤ᵖ B') (S : Cospan B) :
    ((map P).obj S).base = P.obj S.base := sorry

/-- The left leg of a mapped bundled cospan is the image of its left leg. -/
@[simp]
theorem map.obj.fst (P : B ⥤ᵖ B') (S : Cospan B) :
    ((map P).obj S).fst = P.map S.fst := sorry

/-- The right leg of a mapped bundled cospan is the image of its right leg. -/
@[simp]
theorem map.obj.snd (P : B ⥤ᵖ B') (S : Cospan B) :
    ((map P).obj S).snd = P.map S.snd := sorry

/-- Forgetting the bundled wrapper after mapping a cospan morphism gives the canonical mapped
cospan transformation. -/
@[simp]
theorem map.hom.toCospanTransform
    (P : B ⥤ᵖ B') {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.toCospanTransform ((map P).map ψ) =
      CospanTransform.map (Hom.toCospanTransform ψ) P := sorry

/-- Mapping a bundled-cospan morphism applies the ambient pseudofunctor to its left
component. -/
@[simp]
theorem map.hom.left
    (P : B ⥤ᵖ B') {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.left ((map P).map ψ) = P.map (Hom.left ψ) := sorry

/-- Mapping a bundled-cospan morphism applies the ambient pseudofunctor to its right
component. -/
@[simp]
theorem map.hom.right
    (P : B ⥤ᵖ B') {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.right ((map P).map ψ) = P.map (Hom.right ψ) := sorry

/-- Mapping a bundled-cospan morphism applies the ambient pseudofunctor to its common-target
component. -/
@[simp]
theorem map.hom.base
    (P : B ⥤ᵖ B') {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.base ((map P).map ψ) = P.map (Hom.base ψ) := sorry

/-- The left comparison of a mapped bundled-cospan morphism is the canonical
pseudofunctorial pasting. -/
@[simp]
theorem map.hom.leftIso
    (P : B ⥤ᵖ B') {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.leftIso ((map P).map ψ) =
      (P.mapComp (Hom.left ψ) T.fst).symm ≪≫
        P.map₂Iso (Hom.leftIso ψ) ≪≫
          P.mapComp S.fst (Hom.base ψ) := sorry

/-- The right comparison of a mapped bundled-cospan morphism is the canonical
pseudofunctorial pasting. -/
@[simp]
theorem map.hom.rightIso
    (P : B ⥤ᵖ B') {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.rightIso ((map P).map ψ) =
      (P.mapComp (Hom.right ψ) T.snd).symm ≪≫
        P.map₂Iso (Hom.rightIso ψ) ≪≫
          P.mapComp S.snd (Hom.base ψ) := sorry

/-- Forgetting the bundled wrapper after mapping a `2`-morphism gives the canonical mapped
cospan modification. -/
@[simp]
theorem map.map₂.toModification
    (P : B ⥤ᵖ B') {S T : Cospan B} {ψ φ : S ⟶ T}
    (Γ : ψ ⟶ φ) :
    Hom₂.toModification ((map P).map₂ Γ) =
      CospanTransform.Hom.map (Hom₂.toModification Γ) P := sorry

/-- Mapping a bundled-cospan `2`-morphism applies `P.map₂` to its left component. -/
@[simp]
theorem map.map₂.left
    (P : B ⥤ᵖ B') {S T : Cospan B} {ψ φ : S ⟶ T}
    (Γ : ψ ⟶ φ) :
    Hom₂.left ((map P).map₂ Γ) = P.map₂ (Hom₂.left Γ) := sorry

/-- Mapping a bundled-cospan `2`-morphism applies `P.map₂` to its right component. -/
@[simp]
theorem map.map₂.right
    (P : B ⥤ᵖ B') {S T : Cospan B} {ψ φ : S ⟶ T}
    (Γ : ψ ⟶ φ) :
    Hom₂.right ((map P).map₂ Γ) = P.map₂ (Hom₂.right Γ) := sorry

/-- Mapping a bundled-cospan `2`-morphism applies `P.map₂` to its common-target component. -/
@[simp]
theorem map.map₂.base
    (P : B ⥤ᵖ B') {S T : Cospan B} {ψ φ : S ⟶ T}
    (Γ : ψ ⟶ φ) :
    Hom₂.base ((map P).map₂ Γ) = P.map₂ (Hom₂.base Γ) := sorry

end CategoryTheory.Bicategory.Cospan
