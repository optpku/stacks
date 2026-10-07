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
      (Pseudofunctor.compId F).hom := sorry

/-- The factor naturality of `Postcomp.Identity.strongTrans` is the canonical
identity-action comparison. -/
@[simp]
theorem Postcomp.Identity.strongTrans.naturality
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    (Postcomp.Identity.strongTrans A B).naturality η =
      Postcomp.Identity.naturality η := sorry

/-- The forward pointwise component of `Postcomp.Identity.naturality` is the
canonical unitor comparison. -/
@[simp]
theorem Postcomp.Identity.naturality.hom_app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    {F G : Pseudofunctor A B} (η : F ⟶ G) (a : A) :
    (Postcomp.Identity.naturality η).hom.as.app a =
      ((ρ_ (η.app a)) ≪≫ (λ_ (η.app a)).symm).hom := sorry

/-- The inverse pointwise component of `Postcomp.Identity.naturality` is the
inverse canonical unitor comparison. -/
@[simp]
theorem Postcomp.Identity.naturality.inv_app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    {F G : Pseudofunctor A B} (η : F ⟶ G) (a : A) :
    (Postcomp.Identity.naturality η).inv.as.app a =
      ((ρ_ (η.app a)) ≪≫ (λ_ (η.app a)).symm).inv := sorry

/-- The forward strong transformation of `Postcomp.Identity.equivalence` is the explicit
identity-postcomposition comparison. -/
@[simp]
theorem Postcomp.Identity.equivalence.hom
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B] :
    (Postcomp.Identity.equivalence A B).hom = Postcomp.Identity.strongTrans A B := sorry

/-- The forward component of `Postcomp.Identity.equivalence` is the forward component of the
right-unit equivalence of the diagram. -/
@[simp]
theorem Postcomp.Identity.equivalence.hom.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    (F : Pseudofunctor A B) :
    (Postcomp.Identity.equivalence A B).hom.app F = (Pseudofunctor.compId F).hom := sorry

/-- The forward naturality isomorphism of `Postcomp.Identity.equivalence` is the exposed
identity-action factor comparison. -/
@[simp]
theorem Postcomp.Identity.equivalence.hom.naturality
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    {F G : Pseudofunctor A B} (η : F ⟶ G) :
    (Postcomp.Identity.equivalence A B).hom.naturality η =
      Postcomp.Identity.naturality η := sorry

/-- The inverse component of `Postcomp.Identity.equivalence` is the inverse component of the
right-unit equivalence of the diagram. -/
@[simp]
theorem Postcomp.Identity.equivalence.inv.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    (F : Pseudofunctor A B) :
    (Postcomp.Identity.equivalence A B).inv.app F = (Pseudofunctor.compId F).inv := sorry

/-- The inverse factor of `Postcomp.Identity.equivalence` has identity object components. -/
@[simp]
theorem Postcomp.Identity.equivalence.inv.app_app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    (F : Pseudofunctor A B) (a : A) :
    ((Postcomp.Identity.equivalence A B).inv.app F).app a =
      𝟙 ((F.comp (Pseudofunctor.id B)).obj a) := sorry

/-- Evaluating `Postcomp.Identity.equivalence` at a diagram recovers the right-unit
equivalence of that diagram. -/
@[simp]
theorem Postcomp.Identity.equivalence.app
    (A : Type uA) [Bicategory.{wA, vA} A]
    (B : Type uB) [Bicategory.{wB, vB} B]
    (F : Pseudofunctor A B) :
    (Postcomp.Identity.equivalence A B).app F = Pseudofunctor.compId F := sorry

end PostcompositionIdentityComputations

end Pseudofunctor

end CategoryTheory
