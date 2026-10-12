/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Iso.Definition
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Iso.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Operations on Isomorphisms of Telescope Presentations

Compatible isomorphisms of explicit telescope presentations admit identity, inverse, and
composition operations over the corresponding operations on sequential-diagram isomorphisms.
The object-isomorphism and forgetful computations are exposed for downstream rewriting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.Presentation.Iso

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The identity compatible isomorphism of a telescope presentation. -/
@[stacks 0CRH]
def refl {K : ℕ ⥤ D} {X : D} (P : HomotopyColimit.Presentation K X) :
    HomotopyColimit.Presentation.Iso (CategoryTheory.Iso.refl K) P P :=
  HomotopyColimit.Presentation.HomWithIso.id P

/-- Coproduct-to-cocone compatibility for the inverse of a compatible presentation
isomorphism. -/
theorem symm_toCoconeComm {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    CommSq Q.toCocone
      (ColimitCocone.Discrete.map Q.coproduct P.coproduct e.inv.app)
      Φ.iso.inv P.toCocone := sorry

/-- Connecting-map compatibility for the inverse of a compatible presentation
isomorphism. -/
theorem symm_connectingComm {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    CommSq Q.connecting Φ.iso.inv
      ((ColimitCocone.Discrete.map Q.coproduct P.coproduct e.inv.app)⟦(1 : ℤ)⟧')
      P.connecting := sorry

/-- Invert a compatible isomorphism of telescope presentations. -/
@[stacks 0CRH]
def symm {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    HomotopyColimit.Presentation.Iso e.symm Q P where
  iso := Φ.iso.symm
  toCoconeComm := symm_toCoconeComm Φ
  connectingComm := symm_connectingComm Φ

/-- Compose compatible isomorphisms of telescope presentations. -/
@[stacks 0CRH]
def trans {K L M : ℕ ⥤ D} {e : K ≅ L} {f : L ≅ M} {X Y Z : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    {R : HomotopyColimit.Presentation M Z}
    (Φ : HomotopyColimit.Presentation.Iso e P Q)
    (Ψ : HomotopyColimit.Presentation.Iso f Q R) :
    HomotopyColimit.Presentation.Iso (e ≪≫ f) P R :=
  HomotopyColimit.Presentation.HomWithIso.comp Φ Ψ

/-- The object isomorphism of the identity presentation isomorphism is the identity. -/
@[simp]
theorem refl_iso {K : ℕ ⥤ D} {X : D} (P : HomotopyColimit.Presentation K X) :
    (refl P).iso = CategoryTheory.Iso.refl X := sorry

/-- The forward object map of the identity presentation isomorphism is the identity. -/
@[simp]
theorem refl_iso_hom {K : ℕ ⥤ D} {X : D}
    (P : HomotopyColimit.Presentation K X) : (refl P).iso.hom = 𝟙 X := sorry

/-- The inverse object map of the identity presentation isomorphism is the identity. -/
@[simp]
theorem refl_iso_inv {K : ℕ ⥤ D} {X : D}
    (P : HomotopyColimit.Presentation K X) : (refl P).iso.inv = 𝟙 X := sorry

/-- Forgetting the identity presentation isomorphism gives the identity presentation
morphism. -/
@[simp]
theorem refl_toHom {K : ℕ ⥤ D} {X : D} (P : HomotopyColimit.Presentation K X) :
    (refl P).toHom = HomotopyColimit.Presentation.Hom.id P := sorry

/-- The object isomorphism of an inverse presentation isomorphism is the inverse object
isomorphism. -/
@[simp]
theorem symm_iso {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) : Φ.symm.iso = Φ.iso.symm := sorry

/-- The forward object map of an inverse presentation isomorphism is the original inverse
map. -/
@[simp]
theorem symm_iso_hom {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) : Φ.symm.iso.hom = Φ.iso.inv := sorry

/-- The inverse object map of an inverse presentation isomorphism is the original forward
map. -/
@[simp]
theorem symm_iso_inv {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) : Φ.symm.iso.inv = Φ.iso.hom := sorry

/-- The object isomorphism of a composite presentation isomorphism is the composite object
isomorphism. -/
@[simp]
theorem trans_iso
    {K L M : ℕ ⥤ D} {e : K ≅ L} {f : L ≅ M} {X Y Z : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    {R : HomotopyColimit.Presentation M Z}
    (Φ : HomotopyColimit.Presentation.Iso e P Q)
    (Ψ : HomotopyColimit.Presentation.Iso f Q R) :
    (Φ.trans Ψ).iso = Φ.iso ≪≫ Ψ.iso := sorry

/-- The forward object map of a composite presentation isomorphism is the composite of its
forward object maps. -/
@[simp]
theorem trans_iso_hom
    {K L M : ℕ ⥤ D} {e : K ≅ L} {f : L ≅ M} {X Y Z : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    {R : HomotopyColimit.Presentation M Z}
    (Φ : HomotopyColimit.Presentation.Iso e P Q)
    (Ψ : HomotopyColimit.Presentation.Iso f Q R) :
    (Φ.trans Ψ).iso.hom = Φ.iso.hom ≫ Ψ.iso.hom := sorry

/-- The inverse object map of a composite presentation isomorphism is the reverse composite
of its inverse object maps. -/
@[simp]
theorem trans_iso_inv
    {K L M : ℕ ⥤ D} {e : K ≅ L} {f : L ≅ M} {X Y Z : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    {R : HomotopyColimit.Presentation M Z}
    (Φ : HomotopyColimit.Presentation.Iso e P Q)
    (Ψ : HomotopyColimit.Presentation.Iso f Q R) :
    (Φ.trans Ψ).iso.inv = Ψ.iso.inv ≫ Φ.iso.inv := sorry

/-- Forgetting a composite presentation isomorphism gives the composite of the forgotten
presentation morphisms. -/
@[simp]
theorem trans_toHom
    {K L M : ℕ ⥤ D} {e : K ≅ L} {f : L ≅ M} {X Y Z : D}
    {P : HomotopyColimit.Presentation K X} {Q : HomotopyColimit.Presentation L Y}
    {R : HomotopyColimit.Presentation M Z}
    (Φ : HomotopyColimit.Presentation.Iso e P Q)
    (Ψ : HomotopyColimit.Presentation.Iso f Q R) :
    (Φ.trans Ψ).toHom = Φ.toHom.comp Ψ.toHom := sorry

end CategoryTheory.HomotopyColimit.Presentation.Iso
