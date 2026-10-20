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
      (F.mapId x).inv := sorry

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
      F.mapAdj.mapId (Bicategory.Adj.mk x) := sorry

/-- The forward left-adjoint component of the mapped-identity comparison is the
pseudofunctor identity comparison. -/
@[simp]
theorem mapEquivalence.idIso.hom.τl
    (F : Pseudofunctor B C) (x : B) :
    (mapEquivalence.idIso F x).hom.τl = (F.mapId x).hom := sorry

/-- The forward right-adjoint component of the mapped-identity comparison is the inverse
pseudofunctor identity comparison. -/
@[simp]
theorem mapEquivalence.idIso.hom.τr
    (F : Pseudofunctor B C) (x : B) :
    (mapEquivalence.idIso F x).hom.τr = (F.mapId x).inv := sorry

/-- The inverse left-adjoint component of the mapped-identity comparison is the inverse
pseudofunctor identity comparison. -/
@[simp]
theorem mapEquivalence.idIso.inv.τl
    (F : Pseudofunctor B C) (x : B) :
    (mapEquivalence.idIso F x).inv.τl = (F.mapId x).inv := sorry

/-- The inverse right-adjoint component of the mapped-identity comparison is the forward
pseudofunctor identity comparison. -/
@[simp]
theorem mapEquivalence.idIso.inv.τr
    (F : Pseudofunctor B C) (x : B) :
    (mapEquivalence.idIso F x).inv.τr = (F.mapId x).hom := sorry

/-- Reversal of a mapped equivalence and mapping of the reversed equivalence have canonically
mate identity transformations. -/
theorem mapEquivalence.symmIso.conjugate
    (F : Pseudofunctor B C) (e : x ≌ y) :
    conjugateEquiv
        (F.mapEquivalence e).symm.toAdjHom.adj
        (F.mapEquivalence e.symm).toAdjHom.adj
        (𝟙 _) =
      𝟙 _ := sorry

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
    (mapEquivalence.symmIso F e).hom.τl = 𝟙 _ := sorry

/-- The forward right-adjoint component of the mapped-reversal comparison is the identity
`2`-morphism. -/
@[simp]
theorem mapEquivalence.symmIso.hom.τr
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.symmIso F e).hom.τr = 𝟙 _ := sorry

/-- The inverse left-adjoint component of the mapped-reversal comparison is the identity
`2`-morphism. -/
@[simp]
theorem mapEquivalence.symmIso.inv.τl
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.symmIso F e).inv.τl = 𝟙 _ := sorry

/-- The inverse right-adjoint component of the mapped-reversal comparison is the identity
`2`-morphism. -/
@[simp]
theorem mapEquivalence.symmIso.inv.τr
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.symmIso F e).inv.τr = 𝟙 _ := sorry

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
      (F.mapComp e'.inv e.inv).inv := sorry

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
        (F.mapAdj.mapComp e.toAdjHom e'.toAdjHom) := sorry

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
        (F.mapAdj.mapComp e.toAdjHom e'.toAdjHom) := sorry

/-- The forward left-adjoint component of the mapped-composite comparison is the
pseudofunctor composition comparison. -/
@[simp]
theorem mapEquivalence.transIso.hom.τl
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    (mapEquivalence.transIso F e e').hom.τl =
      (F.mapComp e.hom e'.hom).hom := sorry

/-- The forward right-adjoint component of the mapped-composite comparison is the inverse
pseudofunctor comparison for the reverse composite. -/
@[simp]
theorem mapEquivalence.transIso.hom.τr
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    (mapEquivalence.transIso F e e').hom.τr =
      (F.mapComp e'.inv e.inv).inv := sorry

/-- The inverse left-adjoint component of the mapped-composite comparison is the inverse
pseudofunctor composition comparison. -/
@[simp]
theorem mapEquivalence.transIso.inv.τl
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    (mapEquivalence.transIso F e e').inv.τl =
      (F.mapComp e.hom e'.hom).inv := sorry

/-- The inverse right-adjoint component of the mapped-composite comparison is the forward
pseudofunctor comparison for the reverse composite. -/
@[simp]
theorem mapEquivalence.transIso.inv.τr
    (F : Pseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    (mapEquivalence.transIso F e e').inv.τr =
      (F.mapComp e'.inv e.inv).hom := sorry

/-- The identity pseudofunctor gives a mate identity transformation between the mapped
adjunction and the original adjunction. -/
theorem id.mapEquivalenceIso.conjugate (e : x ≌ y) :
    conjugateEquiv e.toAdjHom.adj
        ((Pseudofunctor.id B).mapEquivalence e).toAdjHom.adj
        (𝟙 _) =
      𝟙 _ := sorry

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
    (id.mapEquivalenceIso e).hom.τl = 𝟙 _ := sorry

/-- The forward right-adjoint component of the identity-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem id.mapEquivalenceIso.hom.τr (e : x ≌ y) :
    (id.mapEquivalenceIso e).hom.τr = 𝟙 _ := sorry

/-- The inverse left-adjoint component of the identity-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem id.mapEquivalenceIso.inv.τl (e : x ≌ y) :
    (id.mapEquivalenceIso e).inv.τl = 𝟙 _ := sorry

/-- The inverse right-adjoint component of the identity-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem id.mapEquivalenceIso.inv.τr (e : x ≌ y) :
    (id.mapEquivalenceIso e).inv.τr = 𝟙 _ := sorry

/-- Mapping through the identity pseudofunctor recovers the original equivalence data. This is
the identity law for the pseudofunctor construction, not strict preservation by an arbitrary
pseudofunctor. -/
@[simp]
theorem id_mapEquivalence (e : x ≌ y) :
    (Pseudofunctor.id B).mapEquivalence e = e := sorry

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
      𝟙 _ := sorry

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
    (comp.mapEquivalenceIso F G e).hom.τl = 𝟙 _ := sorry

/-- The forward right-adjoint component of the composite-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem comp.mapEquivalenceIso.hom.τr
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    (comp.mapEquivalenceIso F G e).hom.τr = 𝟙 _ := sorry

/-- The inverse left-adjoint component of the composite-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem comp.mapEquivalenceIso.inv.τl
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    (comp.mapEquivalenceIso F G e).inv.τl = 𝟙 _ := sorry

/-- The inverse right-adjoint component of the composite-pseudofunctor comparison is the
identity `2`-morphism. -/
@[simp]
theorem comp.mapEquivalenceIso.inv.τr
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    (comp.mapEquivalenceIso F G e).inv.τr = 𝟙 _ := sorry

/-- Mapping through a composite pseudofunctor agrees with iterated mapping as an equality of
equivalence data. This is the composition law for the pseudofunctor construction. -/
@[simp]
theorem comp_mapEquivalence
    (F : Pseudofunctor B C) (G : Pseudofunctor C D)
    (e : x ≌ y) :
    (F.comp G).mapEquivalence e =
      G.mapEquivalence (F.mapEquivalence e) := sorry

end Composition

end Pseudofunctor

end CategoryTheory
