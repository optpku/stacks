/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Functoriality.Composition

/-!
# Computations for composition postcomposition coherence

Direct readout lemmas for the direct-to-successive postcomposition comparison.
They expose the inherited pseudofunctor composition equivalences without
requiring downstream users to unfold pointwise-equivalence assembly.
-/

@[expose] public section

universe wA vA uA wB vB uB wD vD uD wE vE uE

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {E : Type uE} [Bicategory.{wE, vE} E]

section PostcompositionCompositionComputations

/-- The component of the direct-to-successive postcomposition strong
transformation is the inverse associativity comparison of the diagram. -/
@[simp]
theorem Postcomp.Composition.strongTrans.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    (F : Pseudofunctor A B) :
    (Postcomp.Composition.strongTrans A K L).app F =
      (Pseudofunctor.compAssoc F K L).symm.hom := rfl

/-- The factor naturality of `Postcomp.Composition.strongTrans` is the canonical
comparison assembled from the objectwise inverse associativity equivalences. -/
@[simp]
theorem Postcomp.Composition.strongTrans.naturality
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    (Postcomp.Composition.strongTrans A K L).naturality η =
      Postcomp.Composition.naturality K L η := rfl

/-- The forward pointwise component of `Postcomp.Composition.naturality` is the
canonical unitor comparison. -/
@[simp]
theorem Postcomp.Composition.naturality.hom_app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    {F G : Pseudofunctor A B} (η : F ⟶ G) (a : A) :
    (Postcomp.Composition.naturality K L η).hom.as.app a =
      ((ρ_ (L.map (K.map (η.app a)))) ≪≫
        (λ_ (L.map (K.map (η.app a)))).symm).hom := rfl

/-- The inverse pointwise component of `Postcomp.Composition.naturality` is the
inverse canonical unitor comparison. -/
@[simp]
theorem Postcomp.Composition.naturality.inv_app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    {F G : Pseudofunctor A B} (η : F ⟶ G) (a : A) :
    (Postcomp.Composition.naturality K L η).inv.as.app a =
      ((ρ_ (L.map (K.map (η.app a)))) ≪≫
        (λ_ (L.map (K.map (η.app a)))).symm).inv := rfl

/-- The forward strong transformation of `Postcomp.Composition.equivalence` is the explicit
direct-to-successive comparison. -/
@[simp]
theorem Postcomp.Composition.equivalence.hom
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E) :
    (Postcomp.Composition.equivalence A K L).hom = Postcomp.Composition.strongTrans A K L := rfl

/-- The forward component of `Postcomp.Composition.equivalence` is the forward component of
the inverse associativity equivalence of the diagram. -/
@[simp]
theorem Postcomp.Composition.equivalence.hom.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    (F : Pseudofunctor A B) :
    (Postcomp.Composition.equivalence A K L).hom.app F =
      (Pseudofunctor.compAssoc F K L).symm.hom := rfl

/-- The forward naturality isomorphism of `Postcomp.Composition.equivalence` is the exposed
factor naturality comparison. -/
@[simp]
theorem Postcomp.Composition.equivalence.hom.naturality
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    (Postcomp.Composition.equivalence A K L).hom.naturality η =
      Postcomp.Composition.naturality K L η := rfl

/-- The inverse component of `Postcomp.Composition.equivalence` is the forward component of
the ordinary associativity equivalence of the diagram. -/
@[simp]
theorem Postcomp.Composition.equivalence.inv.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    (F : Pseudofunctor A B) :
    (Postcomp.Composition.equivalence A K L).inv.app F =
      (Pseudofunctor.compAssoc F K L).hom := rfl

/-- The inverse factor of `Postcomp.Composition.equivalence` has identity object
components. -/
@[simp]
theorem Postcomp.Composition.equivalence.inv.app_app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    (F : Pseudofunctor A B) (a : A) :
    ((Postcomp.Composition.equivalence A K L).inv.app F).app a =
      𝟙 ((F.comp (K.comp L)).obj a) := rfl

/-- Evaluating `Postcomp.Composition.equivalence` at a diagram recovers the inverse
associativity equivalence of that diagram. -/
@[simp]
theorem Postcomp.Composition.equivalence.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (K : Pseudofunctor B D) (L : Pseudofunctor D E)
    (F : Pseudofunctor A B) :
    (Postcomp.Composition.equivalence A K L).app F =
      (Pseudofunctor.compAssoc F K L).symm := by
  dsimp only [Postcomp.Composition.equivalence, Bicategory.Equivalence.app,
    StrictPseudofunctor.mapEquivalence, Pseudofunctor.mapEquivalence,
    StrongTrans.PointwiseEquivalence.toEquivalence]
  congr 1
  · apply Iso.ext
    change 𝟙 _ ≫ ((Pseudofunctor.compAssoc F K L).counit.inv ≫
      (𝟙 _ ▷ (Pseudofunctor.compAssoc F K L).hom)) ≫ 𝟙 _ =
        (Pseudofunctor.compAssoc F K L).counit.inv
    simp only [Bicategory.id_whiskerRight, Category.id_comp, Category.comp_id]
  · apply Iso.ext
    change 𝟙 _ ≫ (((Pseudofunctor.compAssoc F K L).hom ◁ 𝟙 _) ≫
      (Pseudofunctor.compAssoc F K L).unit.inv) ≫ 𝟙 _ =
        (Pseudofunctor.compAssoc F K L).unit.inv
    simp only [Bicategory.whiskerLeft_id, Category.id_comp, Category.comp_id]

end PostcompositionCompositionComputations

end Pseudofunctor

end CategoryTheory
