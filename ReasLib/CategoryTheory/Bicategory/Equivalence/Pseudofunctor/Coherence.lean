/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Pseudofunctor.Mapping
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Composition

/-!
# Coherence for pseudofunctorial equivalence transport

The generic mapping construction is in `Equivalence.Pseudofunctor.Mapping`.
This leaf supplies its canonical mate comparisons for identity, reversal, and
composition, together with their component computations and equality laws.
-/

@[expose] public section

universe w v u w' v' u' w'' v'' u''

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace Pseudofunctor

variable {C : Type u'} [Bicategory.{w', v'} C]
variable {x y : B}

/-- The identity comparison of a pseudofunctor is a mate transformation between the
adjunction underlying the mapped identity equivalence and the target identity adjunction. -/
theorem mapEquivalence.idIso.conjugate
    (F : Pseudofunctor B C) (x : B) :
    conjugateEquiv
        (Bicategory.Equivalence.id (F.obj x)).toAdjHom.adj
        (F.mapEquivalence (Bicategory.Equivalence.id x)).toAdjHom.adj
        (F.mapId x).hom =
      (F.mapId x).inv := by
  rw [conjugateEquiv_apply']
  dsimp [Bicategory.Equivalence.toAdjHom, Bicategory.Equivalence.toAdjunction,
    mapEquivalence, mapEquivalence.unitIso, Bicategory.Equivalence.id]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map,
    whiskerLeft_comp, id_whiskerLeft, unitors_equal, Category.assoc, Iso.inv_hom_id_assoc,
    triangle_assoc_comp_right_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [mapComp_id_left_hom]
  simp only [Category.assoc, unitors_equal, inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id, PrelaxFunctor.map₂_inv_hom, Category.comp_id]

/-- A pseudofunctor preserves the identity bicategorical equivalence up to the canonical
invertible mate transformation in `Bicategory.Adj`. -/
@[stacks 0040 "identity coherence for mapped bicategorical equivalences"]
def mapEquivalence.idIso (F : Pseudofunctor B C) (x : B) :
    (F.mapEquivalence (Bicategory.Equivalence.id x)).toAdjHom ≅
      (Bicategory.Equivalence.id (F.obj x)).toAdjHom :=
  F.mapAdj.mapId (Bicategory.Adj.mk x)

/-- The mapped-identity comparison for equivalences is the identity comparison of the
canonical pseudofunctor action on adjunctions. -/
@[simp]
theorem mapEquivalence.idIso.eq_mapAdj_mapId
    (F : Pseudofunctor B C) (x : B) :
    mapEquivalence.idIso F x =
      F.mapAdj.mapId (Bicategory.Adj.mk x) := by
  rfl

/-- The forward left-adjoint component of the mapped-identity comparison is the
pseudofunctor identity comparison. -/
@[simp]
theorem mapEquivalence.idIso.hom.τl
    (F : Pseudofunctor B C) (x : B) :
    (mapEquivalence.idIso F x).hom.τl = (F.mapId x).hom := by
  rfl

/-- The forward right-adjoint component of the mapped-identity comparison is the inverse
pseudofunctor identity comparison. -/
@[simp]
theorem mapEquivalence.idIso.hom.τr
    (F : Pseudofunctor B C) (x : B) :
    (mapEquivalence.idIso F x).hom.τr = (F.mapId x).inv := by
  rfl

/-- The inverse left-adjoint component of the mapped-identity comparison is the inverse
pseudofunctor identity comparison. -/
@[simp]
theorem mapEquivalence.idIso.inv.τl
    (F : Pseudofunctor B C) (x : B) :
    (mapEquivalence.idIso F x).inv.τl = (F.mapId x).inv := by
  rfl

/-- The inverse right-adjoint component of the mapped-identity comparison is the forward
pseudofunctor identity comparison. -/
@[simp]
theorem mapEquivalence.idIso.inv.τr
    (F : Pseudofunctor B C) (x : B) :
    (mapEquivalence.idIso F x).inv.τr = (F.mapId x).hom := by
  rfl

/-- Reversal of a mapped equivalence and mapping of the reversed equivalence have canonically
mate identity transformations. -/
theorem mapEquivalence.symmIso.conjugate
    (F : Pseudofunctor B C) (e : x ≌ y) :
    conjugateEquiv
        (F.mapEquivalence e).symm.toAdjHom.adj
        (F.mapEquivalence e.symm).toAdjHom.adj
        (𝟙 _) =
      𝟙 _ := by
  have h : (F.mapEquivalence e).symm.toAdjHom.adj =
      (F.mapEquivalence e.symm).toAdjHom.adj := by
    apply Adjunction.ext
    · change ((F.mapId y).inv ≫ F.map₂ e.counit.inv) ≫ (F.mapComp e.inv e.hom).hom =
        (F.mapId y).inv ≫ F.map₂ e.counit.inv ≫ (F.mapComp e.inv e.hom).hom
      simp only [Category.assoc]
    · change ((F.mapComp e.hom e.inv).inv ≫ F.map₂ e.unit.inv) ≫ (F.mapId x).hom =
        (F.mapComp e.hom e.inv).inv ≫ F.map₂ e.unit.inv ≫ (F.mapId x).hom
      simp only [Category.assoc]
  rw [h]
  exact conjugateEquiv_id _

/-- A pseudofunctor commutes with reversal of bicategorical equivalences up to the canonical
invertible mate transformation in `Bicategory.Adj`. -/
@[stacks 0040 "reversal coherence for mapped bicategorical equivalences"]
def mapEquivalence.symmIso
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e.symm).toAdjHom ≅
      (F.mapEquivalence e).symm.toAdjHom :=
  Bicategory.Adj.iso₂Mk (Iso.refl _) (Iso.refl _)
    (mapEquivalence.symmIso.conjugate F e)

/-- The forward left-adjoint component of the mapped-reversal comparison is the identity
`2`-morphism. -/
@[simp]
theorem mapEquivalence.symmIso.hom.τl
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.symmIso F e).hom.τl = 𝟙 _ := by
  rfl

/-- The forward right-adjoint component of the mapped-reversal comparison is the identity
`2`-morphism. -/
@[simp]
theorem mapEquivalence.symmIso.hom.τr
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.symmIso F e).hom.τr = 𝟙 _ := by
  rfl

/-- The inverse left-adjoint component of the mapped-reversal comparison is the identity
`2`-morphism. -/
@[simp]
theorem mapEquivalence.symmIso.inv.τl
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.symmIso F e).inv.τl = 𝟙 _ := by
  rfl

/-- The inverse right-adjoint component of the mapped-reversal comparison is the identity
`2`-morphism. -/
@[simp]
theorem mapEquivalence.symmIso.inv.τr
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.symmIso F e).inv.τr = 𝟙 _ := by
  rfl

/-- The composition comparisons of a pseudofunctor form a mate transformation between the
adjunctions underlying the two ways to map a composite equivalence. -/
theorem mapEquivalence.transIso.conjugate
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    conjugateEquiv
        ((F.mapEquivalence e).trans
          (F.mapEquivalence e')).toAdjHom.adj
        (F.mapEquivalence (e.trans e')).toAdjHom.adj
        (F.mapComp e.hom e'.hom).hom =
      (F.mapComp e'.inv e.inv).inv := by
  have hα {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
      F.map₂ (α_ f g h).inv =
        (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom ≫
          (α_ (F.map f) (F.map g) (F.map h)).inv ≫
            (F.mapComp f g).inv ▷ F.map h ≫ (F.mapComp (f ≫ g) h).inv := by
    apply (cancel_mono (F.map₂ (α_ f g h).hom)).1
    rw [PrelaxFunctor.map₂_inv_hom]
    simp [Category.assoc]
  have hρ {a b : B} (f : a ⟶ b) :
      F.map₂ (ρ_ f).inv = (ρ_ (F.map f)).inv ≫ F.map f ◁ (F.mapId b).inv ≫
        (F.mapComp f (𝟙 b)).inv :=
    F.toLax.map₂_rightUnitor f
  rw [conjugateEquiv_apply,
    ← cancel_epi (ρ_ ((F.mapEquivalence e).trans (F.mapEquivalence e')).toAdjHom.r).hom,
    ← cancel_mono (λ_ (F.mapEquivalence (e.trans e')).toAdjHom.r).inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [mateEquiv_eq_iff]
  simp only [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply]
  simp only [mapEquivalence, mapEquivalence.unitIso, mapEquivalence.counitIso,
    Bicategory.Equivalence.trans, Bicategory.Equivalence.trans.unitIso, bicategoricalIsoComp,
    BicategoricalCoherence.whiskerRight_iso, BicategoricalCoherence.right'_iso,
    BicategoricalCoherence.refl_iso, BicategoricalCoherence.assoc_iso,
    BicategoricalCoherence.assoc'_iso, BicategoricalCoherence.whiskerLeft_iso,
    Bicategory.Equivalence.toAdjHom, Bicategory.Equivalence.toAdjunction, unitors_inv_equal,
    Iso.refl_trans, Iso.trans_refl, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, whiskerRightIso_hom, whiskerLeftIso_hom,
    whiskerLeft_comp, comp_whiskerRight, whisker_assoc, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.refl_hom, whiskerRight_comp, id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id, pentagon_hom_hom_inv_inv_hom, pentagon_inv_inv_hom_hom_inv,
    triangle_assoc_comp_right_inv_assoc, whiskerRight_id, whiskerLeft_rightUnitor,
    comp_whiskerLeft, Iso.hom_inv_id_assoc, Functor.mapIso_trans, Functor.mapIso_symm,
    map₂_whisker_right, PrelaxFunctor.map₂_comp, map₂_associator, map₂_whisker_left,
    whiskerLeft_inv_hom_assoc, Functor.mapIso_inv, id_whiskerLeft, unitors_equal,
    leftUnitor_whiskerRight, triangle_assoc_comp_right_inv, Iso.cancel_iso_inv_left]
  bicategory
  simp [hα, hρ, Category.assoc]

/-- A pseudofunctor preserves composition of bicategorical equivalences up to the canonical
invertible mate transformation in `Bicategory.Adj`. -/
@[stacks 0040 "composition coherence for mapped bicategorical equivalences"]
def mapEquivalence.transIso
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    (F.mapEquivalence (e.trans e')).toAdjHom ≅
      ((F.mapEquivalence e).trans
        (F.mapEquivalence e')).toAdjHom :=
  Bicategory.Adj.iso₂Mk
    (Bicategory.Adj.lIso
      (adj₁ := F.mapAdj.map (e.toAdjHom ≫ e'.toAdjHom))
      (adj₂ := F.mapAdj.map e.toAdjHom ≫
        F.mapAdj.map e'.toAdjHom)
      (F.mapAdj.mapComp e.toAdjHom e'.toAdjHom))
    (Bicategory.Adj.rIso
      (adj₁ := F.mapAdj.map (e.toAdjHom ≫ e'.toAdjHom))
      (adj₂ := F.mapAdj.map e.toAdjHom ≫
        F.mapAdj.map e'.toAdjHom)
      (F.mapAdj.mapComp e.toAdjHom e'.toAdjHom)).symm
    (mapEquivalence.transIso.conjugate F e e')

/-- The left-adjoint isomorphism of the mapped-composite comparison is inherited from the
composition comparison of the canonical pseudofunctor action on adjunctions. -/
@[simp]
theorem mapEquivalence.transIso.lIso
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    Bicategory.Adj.lIso
        (adj₁ := (F.mapEquivalence (e.trans e')).toAdjHom)
        (adj₂ := ((F.mapEquivalence e).trans
          (F.mapEquivalence e')).toAdjHom)
        (mapEquivalence.transIso F e e') =
      Bicategory.Adj.lIso
        (adj₁ := F.mapAdj.map (e.toAdjHom ≫ e'.toAdjHom))
        (adj₂ := F.mapAdj.map e.toAdjHom ≫
          F.mapAdj.map e'.toAdjHom)
        (F.mapAdj.mapComp e.toAdjHom e'.toAdjHom) := by
  rfl

/-- The right-adjoint isomorphism of the mapped-composite comparison is inherited from the
composition comparison of the canonical pseudofunctor action on adjunctions. -/
@[simp]
theorem mapEquivalence.transIso.rIso
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    Bicategory.Adj.rIso
        (adj₁ := (F.mapEquivalence (e.trans e')).toAdjHom)
        (adj₂ := ((F.mapEquivalence e).trans
          (F.mapEquivalence e')).toAdjHom)
        (mapEquivalence.transIso F e e') =
      Bicategory.Adj.rIso
        (adj₁ := F.mapAdj.map (e.toAdjHom ≫ e'.toAdjHom))
        (adj₂ := F.mapAdj.map e.toAdjHom ≫
          F.mapAdj.map e'.toAdjHom)
        (F.mapAdj.mapComp e.toAdjHom e'.toAdjHom) := by
  rfl

/-- The forward left-adjoint component of the mapped-composite comparison is the
pseudofunctor composition comparison. -/
@[simp]
theorem mapEquivalence.transIso.hom.τl
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    (mapEquivalence.transIso F e e').hom.τl =
      (F.mapComp e.hom e'.hom).hom := by
  rfl

/-- The forward right-adjoint component of the mapped-composite comparison is the inverse
pseudofunctor comparison for the reverse composite. -/
@[simp]
theorem mapEquivalence.transIso.hom.τr
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    (mapEquivalence.transIso F e e').hom.τr =
      (F.mapComp e'.inv e.inv).inv := by
  rfl

/-- The inverse left-adjoint component of the mapped-composite comparison is the inverse
pseudofunctor composition comparison. -/
@[simp]
theorem mapEquivalence.transIso.inv.τl
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    (mapEquivalence.transIso F e e').inv.τl =
      (F.mapComp e.hom e'.hom).inv := by
  rfl

/-- The inverse right-adjoint component of the mapped-composite comparison is the forward
pseudofunctor comparison for the reverse composite. -/
@[simp]
theorem mapEquivalence.transIso.inv.τr
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    (mapEquivalence.transIso F e e').inv.τr =
      (F.mapComp e'.inv e.inv).hom := by
  rfl

/-- The identity pseudofunctor gives a mate identity transformation between the mapped
adjunction and the original adjunction. -/
theorem id.mapEquivalenceIso.conjugate (e : x ≌ y) :
    conjugateEquiv e.toAdjHom.adj
        ((Pseudofunctor.id B).mapEquivalence e).toAdjHom.adj
        (𝟙 _) =
      𝟙 _ := by
  have h : ((Pseudofunctor.id B).mapEquivalence e).toAdjHom.adj =
      e.toAdjHom.adj := by
    apply Adjunction.ext
    · change 𝟙 _ ≫ e.unit.hom ≫ 𝟙 _ = e.unit.hom
      simp
    · change 𝟙 _ ≫ e.counit.hom ≫ 𝟙 _ = e.counit.hom
      simp
  rw [h]
  exact conjugateEquiv_id _

/-- Mapping an equivalence through the identity pseudofunctor is canonically isomorphic to its
original adjunction in `Bicategory.Adj`. -/
@[stacks 0040 "identity pseudofunctor coherence for mapped equivalences"]
def id.mapEquivalenceIso (e : x ≌ y) :
    ((Pseudofunctor.id B).mapEquivalence e).toAdjHom ≅
      e.toAdjHom :=
  Bicategory.Adj.iso₂Mk (Iso.refl _) (Iso.refl _)
    (id.mapEquivalenceIso.conjugate e)

/-- The forward left-adjoint component of the identity-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem id.mapEquivalenceIso.hom.τl (e : x ≌ y) :
    (id.mapEquivalenceIso e).hom.τl = 𝟙 _ := by
  rfl

/-- The forward right-adjoint component of the identity-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem id.mapEquivalenceIso.hom.τr (e : x ≌ y) :
    (id.mapEquivalenceIso e).hom.τr = 𝟙 _ := by
  rfl

/-- The inverse left-adjoint component of the identity-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem id.mapEquivalenceIso.inv.τl (e : x ≌ y) :
    (id.mapEquivalenceIso e).inv.τl = 𝟙 _ := by
  rfl

/-- The inverse right-adjoint component of the identity-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem id.mapEquivalenceIso.inv.τr (e : x ≌ y) :
    (id.mapEquivalenceIso e).inv.τr = 𝟙 _ := by
  rfl

/-- Mapping through the identity pseudofunctor recovers the original equivalence data. This is
the identity law for the pseudofunctor construction, not strict preservation by an arbitrary
pseudofunctor. -/
@[simp]
theorem id_mapEquivalence (e : x ≌ y) :
    (Pseudofunctor.id B).mapEquivalence e = e := by
  cases e with
  | mk f g η ε h =>
    dsimp only [mapEquivalence]
    congr 1
    · apply Iso.ext
      change 𝟙 _ ≫ η.hom ≫ 𝟙 _ = η.hom
      simp
    · apply Iso.ext
      change 𝟙 _ ≫ ε.hom ≫ 𝟙 _ = ε.hom
      simp

section Composition

variable {D : Type u''} [Bicategory.{w'', v''} D]

/-- Iterated mapping and mapping through a composite pseudofunctor have canonically mate
identity transformations on their underlying adjunctions. -/
theorem comp.mapEquivalenceIso.conjugate
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    conjugateEquiv
        (G.mapEquivalence (F.mapEquivalence e)).toAdjHom.adj
        ((F.comp G).mapEquivalence e).toAdjHom.adj
        (𝟙 _) =
      𝟙 _ := by
  have h : ((F.comp G).mapEquivalence e).toAdjHom.adj =
      (G.mapEquivalence (F.mapEquivalence e)).toAdjHom.adj := by
    apply Adjunction.ext
    · change ((G.mapId (F.obj x)).inv ≫ G.map₂ (F.mapId x).inv) ≫
          G.map₂ (F.map₂ e.unit.hom) ≫ G.map₂ (F.mapComp e.hom e.inv).hom ≫
            (G.mapComp (F.map e.hom) (F.map e.inv)).hom =
        (G.mapId (F.obj x)).inv ≫
          G.map₂ ((F.mapId x).inv ≫ F.map₂ e.unit.hom ≫ (F.mapComp e.hom e.inv).hom) ≫
            (G.mapComp (F.map e.hom) (F.map e.inv)).hom
      simp only [PrelaxFunctor.map₂_comp, Category.assoc]
    · change ((G.mapComp (F.map e.inv) (F.map e.hom)).inv ≫
          G.map₂ (F.mapComp e.inv e.hom).inv) ≫
            G.map₂ (F.map₂ e.counit.hom) ≫ G.map₂ (F.mapId y).hom ≫
              (G.mapId (F.obj y)).hom =
        (G.mapComp (F.map e.inv) (F.map e.hom)).inv ≫
          G.map₂ ((F.mapComp e.inv e.hom).inv ≫ F.map₂ e.counit.hom ≫ (F.mapId y).hom) ≫
            (G.mapId (F.obj y)).hom
      simp only [PrelaxFunctor.map₂_comp, Category.assoc]
  rw [h]
  exact conjugateEquiv_id _

/-- Mapping an equivalence through a composite pseudofunctor agrees with iterated mapping up
to the canonical invertible mate transformation in `Bicategory.Adj`. -/
@[stacks 0040 "composite pseudofunctor coherence for mapped equivalences"]
def comp.mapEquivalenceIso
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    ((F.comp G).mapEquivalence e).toAdjHom ≅
      (G.mapEquivalence (F.mapEquivalence e)).toAdjHom :=
  Bicategory.Adj.iso₂Mk (Iso.refl _) (Iso.refl _)
    (comp.mapEquivalenceIso.conjugate F G e)

/-- The forward left-adjoint component of the composite-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem comp.mapEquivalenceIso.hom.τl
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    (comp.mapEquivalenceIso F G e).hom.τl = 𝟙 _ := by
  rfl

/-- The forward right-adjoint component of the composite-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem comp.mapEquivalenceIso.hom.τr
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    (comp.mapEquivalenceIso F G e).hom.τr = 𝟙 _ := by
  rfl

/-- The inverse left-adjoint component of the composite-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem comp.mapEquivalenceIso.inv.τl
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    (comp.mapEquivalenceIso F G e).inv.τl = 𝟙 _ := by
  rfl

/-- The inverse right-adjoint component of the composite-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem comp.mapEquivalenceIso.inv.τr
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    (comp.mapEquivalenceIso F G e).inv.τr = 𝟙 _ := by
  rfl

/-- Mapping through a composite pseudofunctor agrees with iterated mapping as an equality of
equivalence data. This is the composition law for the pseudofunctor construction. -/
@[simp]
theorem comp_mapEquivalence
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    (F.comp G).mapEquivalence e =
      G.mapEquivalence (F.mapEquivalence e) := by
  dsimp only [mapEquivalence]
  congr 1
  · apply Iso.ext
    change ((G.mapId (F.obj x)).inv ≫ G.map₂ (F.mapId x).inv) ≫
        G.map₂ (F.map₂ e.unit.hom) ≫ G.map₂ (F.mapComp e.hom e.inv).hom ≫
          (G.mapComp (F.map e.hom) (F.map e.inv)).hom =
      (G.mapId (F.obj x)).inv ≫
        G.map₂ ((F.mapId x).inv ≫ F.map₂ e.unit.hom ≫ (F.mapComp e.hom e.inv).hom) ≫
          (G.mapComp (F.map e.hom) (F.map e.inv)).hom
    simp only [PrelaxFunctor.map₂_comp, Category.assoc]
  · apply Iso.ext
    change ((G.mapComp (F.map e.inv) (F.map e.hom)).inv ≫
        G.map₂ (F.mapComp e.inv e.hom).inv) ≫
          G.map₂ (F.map₂ e.counit.hom) ≫ G.map₂ (F.mapId y).hom ≫
            (G.mapId (F.obj y)).hom =
      (G.mapComp (F.map e.inv) (F.map e.hom)).inv ≫
        G.map₂ ((F.mapComp e.inv e.hom).inv ≫ F.map₂ e.counit.hom ≫ (F.mapId y).hom) ≫
          (G.mapId (F.obj y)).hom
    simp only [PrelaxFunctor.map₂_comp, Category.assoc]

end Composition

end Pseudofunctor

end CategoryTheory
