/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Functoriality.Identity

/-!
# Computations for identity postcomposition coherence

Direct readout lemmas for the identity postcomposition comparison. They expose
the inherited pseudofunctor right-unit equivalences without requiring downstream
users to unfold pointwise-equivalence assembly.
-/

@[expose] public section

universe wA vA uA wB vB uB

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]

section PostcompositionIdentityComputations

/-- The component of the identity-postcomposition strong transformation is the
right-unit comparison of the diagram. -/
@[simp]
theorem Postcomp.Identity.strongTrans.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    (F : Pseudofunctor A B) :
    (Postcomp.Identity.strongTrans A B).app F =
      (Pseudofunctor.compId F).hom := by
  rfl

/-- The factor naturality of `Postcomp.Identity.strongTrans` is the canonical
identity-action comparison. -/
@[simp]
theorem Postcomp.Identity.strongTrans.naturality
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    (Postcomp.Identity.strongTrans A B).naturality η =
      Postcomp.Identity.naturality η := by
  rfl

/-- The forward pointwise component of `Postcomp.Identity.naturality` is the
canonical unitor comparison. -/
@[simp]
theorem Postcomp.Identity.naturality.hom_app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    {F G : Pseudofunctor A B} (η : F ⟶ G) (a : A) :
    (Postcomp.Identity.naturality η).hom.as.app a =
      ((ρ_ (η.app a)) ≪≫ (λ_ (η.app a)).symm).hom := by
  rfl

/-- The inverse pointwise component of `Postcomp.Identity.naturality` is the
inverse canonical unitor comparison. -/
@[simp]
theorem Postcomp.Identity.naturality.inv_app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    {F G : Pseudofunctor A B} (η : F ⟶ G) (a : A) :
    (Postcomp.Identity.naturality η).inv.as.app a =
      ((ρ_ (η.app a)) ≪≫ (λ_ (η.app a)).symm).inv := by
  rfl

/-- The forward strong transformation of `Postcomp.Identity.equivalence` is the explicit
identity-postcomposition comparison. -/
@[simp]
theorem Postcomp.Identity.equivalence.hom
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B] :
    (Postcomp.Identity.equivalence A B).hom = Postcomp.Identity.strongTrans A B := by
  rfl

/-- The forward component of `Postcomp.Identity.equivalence` is the forward component of the
right-unit equivalence of the diagram. -/
@[simp]
theorem Postcomp.Identity.equivalence.hom.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    (F : Pseudofunctor A B) :
    (Postcomp.Identity.equivalence A B).hom.app F = (Pseudofunctor.compId F).hom := by
  rfl

/-- The forward naturality isomorphism of `Postcomp.Identity.equivalence` is the exposed
identity-action factor comparison. -/
@[simp]
theorem Postcomp.Identity.equivalence.hom.naturality
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    (Postcomp.Identity.equivalence A B).hom.naturality η =
      Postcomp.Identity.naturality η := by
  rfl

/-- The inverse component of `Postcomp.Identity.equivalence` is the inverse component of the
right-unit equivalence of the diagram. -/
@[simp]
theorem Postcomp.Identity.equivalence.inv.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    (F : Pseudofunctor A B) :
    (Postcomp.Identity.equivalence A B).inv.app F = (Pseudofunctor.compId F).inv := by
  rfl

/-- The inverse factor of `Postcomp.Identity.equivalence` has identity object components. -/
@[simp]
theorem Postcomp.Identity.equivalence.inv.app_app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    (F : Pseudofunctor A B) (a : A) :
    ((Postcomp.Identity.equivalence A B).inv.app F).app a =
      𝟙 ((F.comp (Pseudofunctor.id B)).obj a) := by
  rfl

/-- Evaluating `Postcomp.Identity.equivalence` at a diagram recovers the right-unit
equivalence of that diagram. -/
@[simp]
theorem Postcomp.Identity.equivalence.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    (F : Pseudofunctor A B) :
    (Postcomp.Identity.equivalence A B).app F = Pseudofunctor.compId F := by
  have ext_equivalence {x y : Pseudofunctor A B} (e e' : x ≌ y)
      (hom : e.hom = e'.hom) (inv : e.inv = e'.inv)
      (unit : HEq e.unit e'.unit) (counit : HEq e.counit e'.counit) : e = e' := by
    cases e
    cases e'
    cases hom
    cases inv
    cases unit
    cases counit
    rfl
  apply ext_equivalence ((Postcomp.Identity.equivalence A B).app F)
    (Pseudofunctor.compId F) rfl rfl
  · apply heq_of_eq
    apply Iso.ext
    change 𝟙 _ ≫ (((Pseudofunctor.compId F).unit.hom ≫
        (𝟙 _ ▷ (Pseudofunctor.compId F).inv)) ≫ 𝟙 _) =
      (Pseudofunctor.compId F).unit.hom
    simp only [Bicategory.id_whiskerRight, Category.id_comp, Category.comp_id]
  · apply heq_of_eq
    apply Iso.ext
    change 𝟙 _ ≫ ((((Pseudofunctor.compId F).inv ◁ 𝟙 _) ≫
        (Pseudofunctor.compId F).counit.hom) ≫ 𝟙 _) =
      (Pseudofunctor.compId F).counit.hom
    simp only [Bicategory.whiskerLeft_id, Category.id_comp, Category.comp_id]

end PostcompositionIdentityComputations

end Pseudofunctor

end CategoryTheory
