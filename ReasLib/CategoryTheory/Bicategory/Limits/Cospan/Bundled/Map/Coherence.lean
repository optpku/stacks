/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Coherence.Computations

/-!
# Coherence computations for mapping bundled bicategorical cospans

This file exposes the identity and composition comparisons of `Cospan.map`. Their underlying
modifications are exactly the canonical walking-cospan comparisons, and their three vertex
components are inherited from the corresponding comparisons of the ambient pseudofunctor.

Functoriality of the construction in the ambient pseudofunctor belongs to a later layer.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']

/-- The forward identity comparison of `Cospan.map` forgets to the canonical mapped-cospan
identity comparison. -/
@[simp]
theorem map.mapId.hom.toModification
    (P : B ⥤ᵖ B') (S : Cospan B) :
    Hom₂.toModification ((map P).mapId S).hom =
      (CospanTransform.map.idIso S.fst S.snd P).hom := sorry

/-- The inverse identity comparison of `Cospan.map` forgets to the inverse canonical
mapped-cospan identity comparison. -/
@[simp]
theorem map.mapId.inv.toModification
    (P : B ⥤ᵖ B') (S : Cospan B) :
    Hom₂.toModification ((map P).mapId S).inv =
      (CospanTransform.map.idIso S.fst S.snd P).inv := sorry

/-- The left component of the forward identity comparison is the ambient identity
comparison at the left endpoint. -/
@[simp]
theorem map.mapId.hom.left
    (P : B ⥤ᵖ B') (S : Cospan B) :
    Hom₂.left ((map P).mapId S).hom =
      (P.mapId S.left).hom := sorry

/-- The right component of the forward identity comparison is the ambient identity
comparison at the right endpoint. -/
@[simp]
theorem map.mapId.hom.right
    (P : B ⥤ᵖ B') (S : Cospan B) :
    Hom₂.right ((map P).mapId S).hom =
      (P.mapId S.right).hom := sorry

/-- The base component of the forward identity comparison is the ambient identity comparison
at the common target. -/
@[simp]
theorem map.mapId.hom.base
    (P : B ⥤ᵖ B') (S : Cospan B) :
    Hom₂.base ((map P).mapId S).hom =
      (P.mapId S.base).hom := sorry

/-- The left component of the inverse identity comparison is the inverse ambient identity
comparison at the left endpoint. -/
@[simp]
theorem map.mapId.inv.left
    (P : B ⥤ᵖ B') (S : Cospan B) :
    Hom₂.left ((map P).mapId S).inv =
      (P.mapId S.left).inv := sorry

/-- The right component of the inverse identity comparison is the inverse ambient identity
comparison at the right endpoint. -/
@[simp]
theorem map.mapId.inv.right
    (P : B ⥤ᵖ B') (S : Cospan B) :
    Hom₂.right ((map P).mapId S).inv =
      (P.mapId S.right).inv := sorry

/-- The base component of the inverse identity comparison is the inverse ambient identity
comparison at the common target. -/
@[simp]
theorem map.mapId.inv.base
    (P : B ⥤ᵖ B') (S : Cospan B) :
    Hom₂.base ((map P).mapId S).inv =
      (P.mapId S.base).inv := sorry

/-- The forward composition comparison of `Cospan.map` forgets to the canonical mapped-cospan
composition comparison. -/
@[simp]
theorem map.mapComp.hom.toModification
    (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    Hom₂.toModification ((map P).mapComp ψ φ).hom =
      (CospanTransform.map.compIso
        (Hom.toCospanTransform ψ) (Hom.toCospanTransform φ) P).hom := sorry

/-- The inverse composition comparison of `Cospan.map` forgets to the inverse canonical
mapped-cospan composition comparison. -/
@[simp]
theorem map.mapComp.inv.toModification
    (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    Hom₂.toModification ((map P).mapComp ψ φ).inv =
      (CospanTransform.map.compIso
        (Hom.toCospanTransform ψ) (Hom.toCospanTransform φ) P).inv := sorry

/-- The left component of the forward composition comparison is the ambient composition
comparison of the left vertex maps. -/
@[simp]
theorem map.mapComp.hom.left
    (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    Hom₂.left ((map P).mapComp ψ φ).hom =
      (P.mapComp (Hom.left ψ) (Hom.left φ)).hom := sorry

/-- The right component of the forward composition comparison is the ambient composition
comparison of the right vertex maps. -/
@[simp]
theorem map.mapComp.hom.right
    (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    Hom₂.right ((map P).mapComp ψ φ).hom =
      (P.mapComp (Hom.right ψ) (Hom.right φ)).hom := sorry

/-- The base component of the forward composition comparison is the ambient composition
comparison of the common-target maps. -/
@[simp]
theorem map.mapComp.hom.base
    (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    Hom₂.base ((map P).mapComp ψ φ).hom =
      (P.mapComp (Hom.base ψ) (Hom.base φ)).hom := sorry

/-- The left component of the inverse composition comparison is the inverse ambient
composition comparison of the left vertex maps. -/
@[simp]
theorem map.mapComp.inv.left
    (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    Hom₂.left ((map P).mapComp ψ φ).inv =
      (P.mapComp (Hom.left ψ) (Hom.left φ)).inv := sorry

/-- The right component of the inverse composition comparison is the inverse ambient
composition comparison of the right vertex maps. -/
@[simp]
theorem map.mapComp.inv.right
    (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    Hom₂.right ((map P).mapComp ψ φ).inv =
      (P.mapComp (Hom.right ψ) (Hom.right φ)).inv := sorry

/-- The base component of the inverse composition comparison is the inverse ambient
composition comparison of the common-target maps. -/
@[simp]
theorem map.mapComp.inv.base
    (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    Hom₂.base ((map P).mapComp ψ φ).inv =
      (P.mapComp (Hom.base ψ) (Hom.base φ)).inv := sorry

end CategoryTheory.Bicategory.Cospan
