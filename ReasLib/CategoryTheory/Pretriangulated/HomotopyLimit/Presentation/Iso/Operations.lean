/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Iso.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Operations on Isomorphisms of Homotopy-Limit Presentations

Compatible isomorphisms of explicit homotopy-limit presentations admit identity, inverse, and
composition operations over the corresponding operations on tower isomorphisms. The object
isomorphism computations are exposed at the bundled, forward-map, and inverse-map levels.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit.Presentation.Iso

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Inclusion compatibility for the identity isomorphism of a homotopy-limit presentation. -/
theorem refl_ιComm {K : SequentialInverseSystem D} {X : D}
    (P : HomotopyLimit.Presentation K X) :
    CommSq P.ι (𝟙 X)
      (ProductCone.map P.product P.product (𝟙 K)) P.ι := sorry

/-- Connecting compatibility for the identity isomorphism of a homotopy-limit presentation. -/
theorem refl_connectingComm {K : SequentialInverseSystem D} {X : D}
    (P : HomotopyLimit.Presentation K X) :
    CommSq P.connecting (ProductCone.map P.product P.product (𝟙 K))
      ((𝟙 X)⟦(1 : ℤ)⟧') P.connecting := sorry

/-- Stacks 08TC: the identity compatible isomorphism of a homotopy-limit presentation. -/
@[stacks 08TC]
def refl {K : SequentialInverseSystem D} {X : D}
    (P : HomotopyLimit.Presentation K X) :
    HomotopyLimit.Presentation.Iso (CategoryTheory.Iso.refl K) P P where
  iso := CategoryTheory.Iso.refl X
  ιComm := refl_ιComm P
  connectingComm := refl_connectingComm P

/-- Inclusion compatibility for the inverse of a compatible presentation isomorphism. -/
theorem symm_ιComm
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    CommSq Q.ι Φ.iso.inv
      (ProductCone.map Q.product P.product e.inv) P.ι := sorry

/-- Connecting compatibility for the inverse of a compatible presentation isomorphism. -/
theorem symm_connectingComm
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    CommSq Q.connecting (ProductCone.map Q.product P.product e.inv)
      (Φ.iso.inv⟦(1 : ℤ)⟧') P.connecting := sorry

/-- Stacks 08TC: invert a compatible isomorphism of homotopy-limit presentations. -/
@[stacks 08TC]
def symm
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    HomotopyLimit.Presentation.Iso e.symm Q P where
  iso := Φ.iso.symm
  ιComm := symm_ιComm Φ
  connectingComm := symm_connectingComm Φ

/-- Inclusion compatibility for a composite of compatible presentation isomorphisms. -/
theorem trans_ιComm
    {K L M : SequentialInverseSystem D} {e : K ≅ L} {f : L ≅ M}
    {X Y Z : D} {P : HomotopyLimit.Presentation K X}
    {Q : HomotopyLimit.Presentation L Y} {R : HomotopyLimit.Presentation M Z}
    (Φ : HomotopyLimit.Presentation.Iso e P Q)
    (Ψ : HomotopyLimit.Presentation.Iso f Q R) :
    CommSq P.ι (Φ.iso ≪≫ Ψ.iso).hom
      (ProductCone.map P.product R.product (e ≪≫ f).hom) R.ι := sorry

/-- Connecting compatibility for a composite of compatible presentation isomorphisms. -/
theorem trans_connectingComm
    {K L M : SequentialInverseSystem D} {e : K ≅ L} {f : L ≅ M}
    {X Y Z : D} {P : HomotopyLimit.Presentation K X}
    {Q : HomotopyLimit.Presentation L Y} {R : HomotopyLimit.Presentation M Z}
    (Φ : HomotopyLimit.Presentation.Iso e P Q)
    (Ψ : HomotopyLimit.Presentation.Iso f Q R) :
    CommSq P.connecting (ProductCone.map P.product R.product (e ≪≫ f).hom)
      ((Φ.iso ≪≫ Ψ.iso).hom⟦(1 : ℤ)⟧') R.connecting := sorry

/-- Stacks 08TC: compose compatible isomorphisms of homotopy-limit presentations. -/
@[stacks 08TC]
def trans
    {K L M : SequentialInverseSystem D} {e : K ≅ L} {f : L ≅ M}
    {X Y Z : D} {P : HomotopyLimit.Presentation K X}
    {Q : HomotopyLimit.Presentation L Y} {R : HomotopyLimit.Presentation M Z}
    (Φ : HomotopyLimit.Presentation.Iso e P Q)
    (Ψ : HomotopyLimit.Presentation.Iso f Q R) :
    HomotopyLimit.Presentation.Iso (e ≪≫ f) P R where
  iso := Φ.iso ≪≫ Ψ.iso
  ιComm := trans_ιComm Φ Ψ
  connectingComm := trans_connectingComm Φ Ψ

/-- The object isomorphism of the identity presentation isomorphism is the identity. -/
@[simp]
theorem refl_iso {K : SequentialInverseSystem D} {X : D}
    (P : HomotopyLimit.Presentation K X) :
    (refl P).iso = CategoryTheory.Iso.refl X := sorry

/-- The forward object map of the identity presentation isomorphism is the identity. -/
@[simp]
theorem refl_iso_hom {K : SequentialInverseSystem D} {X : D}
    (P : HomotopyLimit.Presentation K X) :
    (refl P).iso.hom = 𝟙 X := sorry

/-- The inverse object map of the identity presentation isomorphism is the identity. -/
@[simp]
theorem refl_iso_inv {K : SequentialInverseSystem D} {X : D}
    (P : HomotopyLimit.Presentation K X) :
    (refl P).iso.inv = 𝟙 X := sorry

/-- The object isomorphism of an inverse presentation isomorphism is the inverse object
isomorphism. -/
@[simp]
theorem symm_iso
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    Φ.symm.iso = Φ.iso.symm := sorry

/-- The forward object map of an inverse presentation isomorphism is the original inverse map. -/
@[simp]
theorem symm_iso_hom
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    Φ.symm.iso.hom = Φ.iso.inv := sorry

/-- The inverse object map of an inverse presentation isomorphism is the original forward map. -/
@[simp]
theorem symm_iso_inv
    {K L : SequentialInverseSystem D} {e : K ≅ L} {X Y : D}
    {P : HomotopyLimit.Presentation K X} {Q : HomotopyLimit.Presentation L Y}
    (Φ : HomotopyLimit.Presentation.Iso e P Q) :
    Φ.symm.iso.inv = Φ.iso.hom := sorry

/-- The object isomorphism of a composite presentation isomorphism is the composite of the
object isomorphisms. -/
@[simp]
theorem trans_iso
    {K L M : SequentialInverseSystem D} {e : K ≅ L} {f : L ≅ M}
    {X Y Z : D} {P : HomotopyLimit.Presentation K X}
    {Q : HomotopyLimit.Presentation L Y} {R : HomotopyLimit.Presentation M Z}
    (Φ : HomotopyLimit.Presentation.Iso e P Q)
    (Ψ : HomotopyLimit.Presentation.Iso f Q R) :
    (Φ.trans Ψ).iso = Φ.iso ≪≫ Ψ.iso := sorry

/-- The forward object map of a composite presentation isomorphism is the composite of the
forward object maps. -/
@[simp]
theorem trans_iso_hom
    {K L M : SequentialInverseSystem D} {e : K ≅ L} {f : L ≅ M}
    {X Y Z : D} {P : HomotopyLimit.Presentation K X}
    {Q : HomotopyLimit.Presentation L Y} {R : HomotopyLimit.Presentation M Z}
    (Φ : HomotopyLimit.Presentation.Iso e P Q)
    (Ψ : HomotopyLimit.Presentation.Iso f Q R) :
    (Φ.trans Ψ).iso.hom = Φ.iso.hom ≫ Ψ.iso.hom := sorry

/-- The inverse object map of a composite presentation isomorphism is the reverse composite of
the inverse object maps. -/
@[simp]
theorem trans_iso_inv
    {K L M : SequentialInverseSystem D} {e : K ≅ L} {f : L ≅ M}
    {X Y Z : D} {P : HomotopyLimit.Presentation K X}
    {Q : HomotopyLimit.Presentation L Y} {R : HomotopyLimit.Presentation M Z}
    (Φ : HomotopyLimit.Presentation.Iso e P Q)
    (Ψ : HomotopyLimit.Presentation.Iso f Q R) :
    (Φ.trans Ψ).iso.inv = Ψ.iso.inv ≫ Φ.iso.inv := sorry

end CategoryTheory.HomotopyLimit.Presentation.Iso
