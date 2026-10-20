/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Composition.Associativity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Composition.Identity

/-!
# Computations for pseudofunctor-composition coherence

Direct readout lemmas for the associativity and unit equivalences of
pseudofunctor composition.  They retain the concrete identity components and
unitor naturality comparisons without unfolding pointwise-equivalence
assembly.
-/

@[expose] public section

universe wB vB uB wC vC uC wD vD uD wE vE uE

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {E : Type uE} [Bicategory.{wE, vE} E]


/-- The components of `compAssoc.strongTrans` are identity `1`-morphisms. -/
@[simp]
theorem compAssoc.strongTrans.app
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E)
    (a : B) :
    (compAssoc.strongTrans F G H).app a =
      𝟙 ((F.comp (G.comp H)).obj a) := sorry

/-- The naturality comparison of `compAssoc.strongTrans` is the canonical
right-unitor followed by the inverse left-unitor. -/
@[simp]
theorem compAssoc.strongTrans.naturality
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E)
    {a b : B} (f : a ⟶ b) :
    (compAssoc.strongTrans F G H).naturality f =
      (ρ_ (((F.comp G).comp H).map f)) ≪≫
        (λ_ ((F.comp (G.comp H)).map f)).symm := sorry

/-- The pointwise equivalence behind `compAssoc` is the identity equivalence. -/
@[simp]
theorem compAssoc.pointwiseEquivalence.app
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E)
    (a : B) :
    (compAssoc.pointwiseEquivalence F G H).app a =
      Bicategory.Equivalence.id ((F.comp (G.comp H)).obj a) := sorry

/-- The forward strong transformation of `compAssoc` is its explicit
associativity comparison. -/
@[simp]
theorem compAssoc.hom
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E) :
    (compAssoc F G H).hom = compAssoc.strongTrans F G H := sorry

/-- The forward components of `compAssoc` are identity `1`-morphisms. -/
@[simp]
theorem compAssoc.hom.app
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E)
    (a : B) :
    (compAssoc F G H).hom.app a =
      𝟙 ((F.comp (G.comp H)).obj a) := sorry

/-- The forward naturality comparison of `compAssoc` is the canonical unitor
comparison. -/
@[simp]
theorem compAssoc.hom.naturality
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E)
    {a b : B} (f : a ⟶ b) :
    (compAssoc F G H).hom.naturality f =
      (ρ_ (((F.comp G).comp H).map f)) ≪≫
        (λ_ ((F.comp (G.comp H)).map f)).symm := sorry

/-- The inverse components of `compAssoc` are identity `1`-morphisms. -/
@[simp]
theorem compAssoc.inv.app
    (F : Pseudofunctor B C) (G : Pseudofunctor C D) (H : Pseudofunctor D E)
    (a : B) :
    (compAssoc F G H).inv.app a =
      𝟙 (((F.comp G).comp H).obj a) := sorry

/-- The components of `idComp.strongTrans` are identity `1`-morphisms. -/
@[simp]
theorem idComp.strongTrans.app (F : Pseudofunctor B C) (a : B) :
    (idComp.strongTrans F).app a = 𝟙 (F.obj a) := sorry

/-- The naturality comparison of `idComp.strongTrans` is the canonical
right-unitor followed by the inverse left-unitor. -/
@[simp]
theorem idComp.strongTrans.naturality
    (F : Pseudofunctor B C) {a b : B} (f : a ⟶ b) :
    (idComp.strongTrans F).naturality f =
      (ρ_ (((Pseudofunctor.id B).comp F).map f)) ≪≫ (λ_ (F.map f)).symm := sorry

/-- The pointwise equivalence behind `idComp` is the identity equivalence. -/
@[simp]
theorem idComp.pointwiseEquivalence.app
    (F : Pseudofunctor B C) (a : B) :
    (idComp.pointwiseEquivalence F).app a =
      Bicategory.Equivalence.id (F.obj a) := sorry

/-- The forward strong transformation of `idComp` is its explicit left-unit
comparison. -/
@[simp]
theorem idComp.hom (F : Pseudofunctor B C) :
    (idComp F).hom = idComp.strongTrans F := sorry

/-- The forward components of `idComp` are identity `1`-morphisms. -/
@[simp]
theorem idComp.hom.app (F : Pseudofunctor B C) (a : B) :
    (idComp F).hom.app a = 𝟙 (F.obj a) := sorry

/-- The forward naturality comparison of `idComp` is the canonical unitor
comparison. -/
@[simp]
theorem idComp.hom.naturality
    (F : Pseudofunctor B C) {a b : B} (f : a ⟶ b) :
    (idComp F).hom.naturality f =
      (ρ_ (((Pseudofunctor.id B).comp F).map f)) ≪≫ (λ_ (F.map f)).symm := sorry

/-- The inverse components of `idComp` are identity `1`-morphisms. -/
@[simp]
theorem idComp.inv.app (F : Pseudofunctor B C) (a : B) :
    (idComp F).inv.app a = 𝟙 (((Pseudofunctor.id B).comp F).obj a) := sorry

/-- The components of `compId.strongTrans` are identity `1`-morphisms. -/
@[simp]
theorem compId.strongTrans.app (F : Pseudofunctor B C) (a : B) :
    (compId.strongTrans F).app a = 𝟙 (F.obj a) := sorry

/-- The naturality comparison of `compId.strongTrans` is the canonical
right-unitor followed by the inverse left-unitor. -/
@[simp]
theorem compId.strongTrans.naturality
    (F : Pseudofunctor B C) {a b : B} (f : a ⟶ b) :
    (compId.strongTrans F).naturality f =
      (ρ_ ((F.comp (Pseudofunctor.id C)).map f)) ≪≫ (λ_ (F.map f)).symm := sorry

/-- The pointwise equivalence behind `compId` is the identity equivalence. -/
@[simp]
theorem compId.pointwiseEquivalence.app
    (F : Pseudofunctor B C) (a : B) :
    (compId.pointwiseEquivalence F).app a =
      Bicategory.Equivalence.id (F.obj a) := sorry

/-- The forward strong transformation of `compId` is its explicit right-unit
comparison. -/
@[simp]
theorem compId.hom (F : Pseudofunctor B C) :
    (compId F).hom = compId.strongTrans F := sorry

/-- The forward components of `compId` are identity `1`-morphisms. -/
@[simp]
theorem compId.hom.app (F : Pseudofunctor B C) (a : B) :
    (compId F).hom.app a = 𝟙 (F.obj a) := sorry

/-- The forward naturality comparison of `compId` is the canonical unitor
comparison. -/
@[simp]
theorem compId.hom.naturality
    (F : Pseudofunctor B C) {a b : B} (f : a ⟶ b) :
    (compId F).hom.naturality f =
      (ρ_ ((F.comp (Pseudofunctor.id C)).map f)) ≪≫ (λ_ (F.map f)).symm := sorry

/-- The inverse components of `compId` are identity `1`-morphisms. -/
@[simp]
theorem compId.inv.app (F : Pseudofunctor B C) (a : B) :
    (compId F).inv.app a = 𝟙 ((F.comp (Pseudofunctor.id C)).obj a) := sorry

end Pseudofunctor

end CategoryTheory
