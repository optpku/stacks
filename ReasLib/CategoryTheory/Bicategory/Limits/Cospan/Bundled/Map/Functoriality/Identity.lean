/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Coherence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Functoriality.Identity.Basic

/-!
# Computations for identity functoriality on bundled cospans

The naturality comparison `Cospan.mapIdentity.naturalityIso` computes at each cospan vertex to the
standard naturality comparison of an identity strong transformation. These formulas hide the
induced-bicategory wrapper and make the comparison directly usable by componentwise proofs.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T : Cospan B}

/-- The forward left component of identity-mapping naturality is the standard unitor
comparison. -/
@[simp]
theorem mapIdentity.naturalityIso.hom.left (ψ : S ⟶ T) :
    Hom₂.left (mapIdentity.naturalityIso ψ).hom =
      (ρ_ (Hom.left ψ)).hom ≫ (λ_ (Hom.left ψ)).inv := sorry

/-- The forward right component of identity-mapping naturality is the standard unitor
comparison. -/
@[simp]
theorem mapIdentity.naturalityIso.hom.right (ψ : S ⟶ T) :
    Hom₂.right (mapIdentity.naturalityIso ψ).hom =
      (ρ_ (Hom.right ψ)).hom ≫ (λ_ (Hom.right ψ)).inv := sorry

/-- The forward base component of identity-mapping naturality is the standard unitor
comparison. -/
@[simp]
theorem mapIdentity.naturalityIso.hom.base (ψ : S ⟶ T) :
    Hom₂.base (mapIdentity.naturalityIso ψ).hom =
      (ρ_ (Hom.base ψ)).hom ≫ (λ_ (Hom.base ψ)).inv := sorry

/-- The inverse left component of identity-mapping naturality is the inverse standard unitor
comparison. -/
@[simp]
theorem mapIdentity.naturalityIso.inv.left (ψ : S ⟶ T) :
    Hom₂.left (mapIdentity.naturalityIso ψ).inv =
      (λ_ (Hom.left ψ)).hom ≫ (ρ_ (Hom.left ψ)).inv := sorry

/-- The inverse right component of identity-mapping naturality is the inverse standard unitor
comparison. -/
@[simp]
theorem mapIdentity.naturalityIso.inv.right (ψ : S ⟶ T) :
    Hom₂.right (mapIdentity.naturalityIso ψ).inv =
      (λ_ (Hom.right ψ)).hom ≫ (ρ_ (Hom.right ψ)).inv := sorry

/-- The inverse base component of identity-mapping naturality is the inverse standard unitor
comparison. -/
@[simp]
theorem mapIdentity.naturalityIso.inv.base (ψ : S ⟶ T) :
    Hom₂.base (mapIdentity.naturalityIso ψ).inv =
      (λ_ (Hom.base ψ)).hom ≫ (ρ_ (Hom.base ψ)).inv := sorry

end CategoryTheory.Bicategory.Cospan
