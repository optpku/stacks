module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Functoriality.Identity

/-!
# Computations for identity coherence of precomposition

Readout lemmas for precomposition by the identity pseudofunctor.  The API
keeps the objectwise `Pseudofunctor.idComp` equivalences visible in both the
forward and inverse directions.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]

section PrecompositionFunctoriality

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable (B) (D) in
/-- The object component of the precomposition-identity comparison is the
ordinary left-unit equivalence of pseudofunctor composition. -/
@[simp]
theorem Precomp.Identity.strongTrans.app
    (F : Pseudofunctor B D) :
    (Precomp.Identity.strongTrans B D).app F =
      (Pseudofunctor.idComp F).hom := sorry

/-- The factor naturality of `Precomp.Identity.strongTrans` is the canonical
identity-action comparison. -/
@[simp]
theorem Precomp.Identity.strongTrans.naturality
    {F G : Pseudofunctor B D} (η : F ⟶ G) :
    (Precomp.Identity.strongTrans B D).naturality η =
      Precomp.Identity.naturality η := sorry

/-- The forward component of the identity-action naturality comparison is the
right-unitor followed by the inverse left-unitor. -/
@[simp]
theorem Precomp.Identity.naturality.hom_app
    {F G : Pseudofunctor B D} (η : F ⟶ G) (b : B) :
    (Precomp.Identity.naturality η).hom.as.app b =
      ((ρ_ (η.app b)) ≪≫ (λ_ (η.app b)).symm).hom := sorry

/-- The inverse component of the identity-action naturality comparison is the
inverse of the right-unitor/inverse-left-unitor composite. -/
@[simp]
theorem Precomp.Identity.naturality.inv_app
    {F G : Pseudofunctor B D} (η : F ⟶ G) (b : B) :
    (Precomp.Identity.naturality η).inv.as.app b =
      ((ρ_ (η.app b)) ≪≫ (λ_ (η.app b)).symm).inv := sorry

variable (B) (D) in
/-- The pointwise equivalence of `Precomp.Identity.equivalence` is exactly
`Pseudofunctor.idComp`. -/
@[simp]
theorem Precomp.Identity.equivalence.app
    (F : Pseudofunctor B D) :
    (Precomp.Identity.equivalence B D).app F = Pseudofunctor.idComp F := sorry

variable (B) (D) in
/-- The forward strong transformation of `Precomp.Identity.equivalence` is the explicit
precomposition-identity factor comparison. -/
@[simp]
theorem Precomp.Identity.equivalence.hom :
    (Precomp.Identity.equivalence B D).hom = Precomp.Identity.strongTrans B D := sorry

variable (B) (D) in
/-- The forward component of `Precomp.Identity.equivalence` at a diagram is the forward
component of `Pseudofunctor.idComp`. -/
@[simp]
theorem Precomp.Identity.equivalence.hom.app
    (F : Pseudofunctor B D) :
    (Precomp.Identity.equivalence B D).hom.app F = (Pseudofunctor.idComp F).hom := sorry

variable (B) (D) in
/-- The forward naturality isomorphism of `Precomp.Identity.equivalence` is the exposed
identity-action factor comparison. -/
@[simp]
theorem Precomp.Identity.equivalence.hom.naturality
    {F G : Pseudofunctor B D} (η : F ⟶ G) :
    (Precomp.Identity.equivalence B D).hom.naturality η =
      Precomp.Identity.naturality η := sorry

variable (B) (D) in
/-- The inverse component of `Precomp.Identity.equivalence` at a diagram is the inverse
component of `Pseudofunctor.idComp`. -/
@[simp]
theorem Precomp.Identity.equivalence.inv.app
    (F : Pseudofunctor B D) :
    (Precomp.Identity.equivalence B D).inv.app F = (Pseudofunctor.idComp F).inv := sorry

variable (B) (D) in
/-- The inverse factor of `Precomp.Identity.equivalence` has identity object components. -/
@[simp]
theorem Precomp.Identity.equivalence.inv.app_app
    (F : Pseudofunctor B D) (b : B) :
    ((Precomp.Identity.equivalence B D).inv.app F).app b =
      𝟙 (((Pseudofunctor.id B).comp F).obj b) := sorry

end PrecompositionFunctoriality

end Pseudofunctor

end CategoryTheory
