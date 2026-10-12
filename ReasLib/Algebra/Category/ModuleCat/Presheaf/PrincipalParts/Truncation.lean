/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.Truncation

/-!
# Truncation of principal-parts presheaves

The algebraic transition `PrincipalParts.RingHom.truncate σ M h` for `h : k ≤ l` is compatible
with restriction maps and with morphisms of module presheaves. It therefore defines both a
morphism of principal-parts presheaves and a natural transformation between the corresponding
endofunctors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace PresheafOfModules.PrincipalParts

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : O₁ ⟶ O₂)
variable (F : PresheafOfModules (ringPresheaf O₂))

/-- The objectwise truncation from principal parts of order `l` to order `k`. -/
noncomputable abbrev truncateApp {k l : ℕ} (h : k ≤ l) (X : Cᵒᵖ) :
    module φ F l X ⟶ module φ F k X :=
  _root_.PrincipalParts.RingHom.truncate (φ.app X).hom (F.obj X) h

/-- Objectwise truncation preserves the universal class of every section. -/
@[simp]
theorem truncateApp_universalClass {k l : ℕ} (h : k ≤ l)
    (X : Cᵒᵖ) (m : F.obj X) :
    (truncateApp φ F h X).hom (universalClass φ F l X m) =
      universalClass φ F k X m := sorry

/-- Every objectwise principal-parts truncation is surjective. -/
theorem truncateApp_surjective {k l : ℕ} (h : k ≤ l) (X : Cᵒᵖ) :
    Function.Surjective (truncateApp φ F h X) := sorry

/-- Objectwise truncation commutes with restriction along every morphism of the site. -/
theorem truncateApp_naturality {k l : ℕ} (h : k ≤ l)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    restrictionMap φ F l f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (truncateApp φ F h Y) =
      truncateApp φ F h X ≫ restrictionMap φ F k f := sorry

/-- Tag 09CL: the truncation morphism between principal-parts presheaves of orders `l` and `k`. -/
@[stacks 09CL "presheaf order truncation"]
noncomputable def truncate {k l : ℕ} (h : k ≤ l) :
    presheaf φ F l ⟶ presheaf φ F k where
  app X := truncateApp φ F h X
  naturality f := truncateApp_naturality φ F h f

/-- Every truncation morphism of principal-parts presheaves is an epimorphism. -/
instance truncate_epi {k l : ℕ} (h : k ≤ l) : Epi (truncate φ F h) := sorry

/-- Presheaf truncation along a reflexive order comparison is the identity. -/
@[simp]
theorem truncate_refl (k : ℕ) :
    truncate φ F (le_refl k) = 𝟙 (presheaf φ F k) := sorry

/-- Successive presheaf truncations equal truncation along the composite order comparison. -/
@[simp]
theorem truncate_trans {k l n : ℕ} (hkl : k ≤ l) (hln : l ≤ n) :
    truncate φ F hln ≫ truncate φ F hkl = truncate φ F (hkl.trans hln) := sorry

section Naturality

variable {G : PresheafOfModules (ringPresheaf O₂)}

/-- Presheaf truncation is natural with respect to morphisms of module presheaves. -/
theorem truncate_naturality {k l : ℕ} (h : k ≤ l) (α : F ⟶ G) :
    map φ F l α ≫ truncate φ G h = truncate φ F h ≫ map φ F k α := sorry

end Naturality

/-- Truncation in the order bound is a natural transformation between principal-parts
endofunctors. -/
noncomputable def truncateNatTrans {k l : ℕ} (h : k ≤ l) :
    functor φ l ⟶ functor φ k where
  app F := truncate φ F h
  naturality {F G} α := truncate_naturality φ F (G := G) h α

end PresheafOfModules.PrincipalParts
