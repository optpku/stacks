/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Functoriality.Composition

/-!
# Computations for composition coherence of precomposition

Readout lemmas for the equivalence between direct precomposition by a composite
and successive precomposition.  The API retains the objectwise
`Pseudofunctor.compAssoc` factors and exposes both directions of the resulting
equivalence.
-/

@[expose] public section

universe wA vA uA wB vB uB wC vC uC wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {D : Type uD} [Bicategory.{wD, vD} D]

section PrecompositionFunctoriality

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable (D) in
/-- The object component of direct-to-successive precomposition is the
ordinary associativity equivalence of pseudofunctor composition. -/
@[simp]
theorem Precomp.Composition.strongTrans.app
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    (F : Pseudofunctor C D) :
    (Precomp.Composition.strongTrans D H K).app F =
      (Pseudofunctor.compAssoc H K F).hom := sorry

/-- The factor naturality of `Precomp.Composition.strongTrans` is the canonical
comparison assembled from the component associators. -/
@[simp]
theorem Precomp.Composition.strongTrans.naturality
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    {F G : Pseudofunctor C D} (η : F ⟶ G) :
    (Precomp.Composition.strongTrans D H K).naturality η =
      Precomp.Composition.naturality H K η := sorry

/-- The forward component of the factor naturality comparison is the
right-unitor followed by the inverse left-unitor. -/
@[simp]
theorem Precomp.Composition.naturality.hom_app
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    {F G : Pseudofunctor C D} (η : F ⟶ G) (a : A) :
    (Precomp.Composition.naturality H K η).hom.as.app a =
      ((ρ_ (η.app ((H.comp K).obj a))) ≪≫
        (λ_ (η.app ((H.comp K).obj a))).symm).hom := sorry

/-- The inverse component of the factor naturality comparison is the inverse
of the right-unitor/inverse-left-unitor composite. -/
@[simp]
theorem Precomp.Composition.naturality.inv_app
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    {F G : Pseudofunctor C D} (η : F ⟶ G) (a : A) :
    (Precomp.Composition.naturality H K η).inv.as.app a =
      ((ρ_ (η.app ((H.comp K).obj a))) ≪≫
        (λ_ (η.app ((H.comp K).obj a))).symm).inv := sorry

variable (D) in
/-- The pointwise equivalence of `Precomp.Composition.equivalence` is exactly
`Pseudofunctor.compAssoc`. -/
@[simp]
theorem Precomp.Composition.equivalence.app
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    (F : Pseudofunctor C D) :
    (Precomp.Composition.equivalence D H K).app F = Pseudofunctor.compAssoc H K F := sorry

variable (D) in
/-- The forward strong transformation of `Precomp.Composition.equivalence` is its explicit
direct-to-successive factor comparison. -/
@[simp]
theorem Precomp.Composition.equivalence.hom
    (H : Pseudofunctor A B) (K : Pseudofunctor B C) :
    (Precomp.Composition.equivalence D H K).hom = Precomp.Composition.strongTrans D H K := sorry

variable (D) in
/-- The forward component of `Precomp.Composition.equivalence` at a diagram is the forward
component of `Pseudofunctor.compAssoc`. -/
@[simp]
theorem Precomp.Composition.equivalence.hom.app
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    (F : Pseudofunctor C D) :
    (Precomp.Composition.equivalence D H K).hom.app F =
      (Pseudofunctor.compAssoc H K F).hom := sorry

variable (D) in
/-- The forward naturality isomorphism of `Precomp.Composition.equivalence` is the exposed
factor naturality comparison. -/
@[simp]
theorem Precomp.Composition.equivalence.hom.naturality
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    {F G : Pseudofunctor C D} (η : F ⟶ G) :
    (Precomp.Composition.equivalence D H K).hom.naturality η =
      Precomp.Composition.naturality H K η := sorry

variable (D) in
/-- The inverse component of `Precomp.Composition.equivalence` at a diagram is the inverse
component of `Pseudofunctor.compAssoc`. -/
@[simp]
theorem Precomp.Composition.equivalence.inv.app
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    (F : Pseudofunctor C D) :
    (Precomp.Composition.equivalence D H K).inv.app F =
      (Pseudofunctor.compAssoc H K F).inv := sorry

variable (D) in
/-- The inverse factor of `Precomp.Composition.equivalence` has identity object components. -/
@[simp]
theorem Precomp.Composition.equivalence.inv.app_app
    (H : Pseudofunctor A B) (K : Pseudofunctor B C)
    (F : Pseudofunctor C D) (a : A) :
    ((Precomp.Composition.equivalence D H K).inv.app F).app a =
      𝟙 (((H.comp K).comp F).obj a) := sorry

end PrecompositionFunctoriality

end Pseudofunctor

end CategoryTheory
