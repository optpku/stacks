module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Two-chart affine open covers with affine overlap

A scheme `X` together with affine opens `U₁`, `U₂` whose overlap is affine and
whose union is `X`. The associated rings are the section rings `Γ(X, Uᵢ)`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A covering of a scheme by two affine opens with affine overlap. -/
structure TwoAffineOpenCover (X : Scheme.{u}) : Type u where
  /-- The first affine open. -/
  U₁ : X.Opens
  /-- The second affine open. -/
  U₂ : X.Opens
  /-- `U₁` is affine. -/
  isAffine_U₁ : IsAffineOpen U₁
  /-- `U₂` is affine. -/
  isAffine_U₂ : IsAffineOpen U₂
  /-- The overlap `U₁ ⊓ U₂` is affine. -/
  isAffine_inf : IsAffineOpen (U₁ ⊓ U₂)
  /-- The two opens cover `X`. -/
  sup_eq_top : U₁ ⊔ U₂ = ⊤

namespace TwoAffineOpenCover

variable {X : Scheme.{u}}

/-- Package two affine opens with affine overlap covering `X`. -/
def of (U₁ U₂ : X.Opens) (isAffine_U₁ : IsAffineOpen U₁) (isAffine_U₂ : IsAffineOpen U₂)
    (isAffine_inf : IsAffineOpen (U₁ ⊓ U₂)) (sup_eq_top : U₁ ⊔ U₂ = ⊤) :
    TwoAffineOpenCover X where
  U₁ := U₁
  U₂ := U₂
  isAffine_U₁ := isAffine_U₁
  isAffine_U₂ := isAffine_U₂
  isAffine_inf := isAffine_inf
  sup_eq_top := sup_eq_top

/-- A two-chart affine cover consists of two affine opens with affine overlap covering `X`. -/
theorem spec (c : TwoAffineOpenCover X) :
    IsAffineOpen c.U₁ ∧ IsAffineOpen c.U₂ ∧ IsAffineOpen (c.U₁ ⊓ c.U₂) ∧ c.U₁ ⊔ c.U₂ = ⊤ :=
  sorry

/-- The overlap open `U₁ ⊓ U₂`. -/
abbrev inf (c : TwoAffineOpenCover X) : X.Opens :=
  c.U₁ ⊓ c.U₂

/-- The section ring `P₁ = Γ(X, U₁)`. -/
abbrev ring₁ (c : TwoAffineOpenCover X) : Type u :=
  Γ(X, c.U₁)

/-- The section ring `P₂ = Γ(X, U₂)`. -/
abbrev ring₂ (c : TwoAffineOpenCover X) : Type u :=
  Γ(X, c.U₂)

/-- The section ring `P₁₂ = Γ(X, U₁ ⊓ U₂)`. -/
abbrev ringInf (c : TwoAffineOpenCover X) : Type u :=
  Γ(X, c.U₁ ⊓ c.U₂)

/-- The canonical identification `U₁ ≅ Spec Γ(X, U₁)`. -/
def isoSpec₁ (c : TwoAffineOpenCover X) : c.U₁.toScheme ≅ Spec Γ(X, c.U₁) :=
  c.isAffine_U₁.isoSpec

/-- The canonical identification `U₂ ≅ Spec Γ(X, U₂)`. -/
def isoSpec₂ (c : TwoAffineOpenCover X) : c.U₂.toScheme ≅ Spec Γ(X, c.U₂) :=
  c.isAffine_U₂.isoSpec

/-- The canonical identification `U₁ ⊓ U₂ ≅ Spec Γ(X, U₁ ⊓ U₂)`. -/
def isoSpecInf (c : TwoAffineOpenCover X) :
    (c.U₁ ⊓ c.U₂).toScheme ≅ Spec Γ(X, c.U₁ ⊓ c.U₂) :=
  c.isAffine_inf.isoSpec

/-- The open immersion `Spec Γ(X, U₁) ⟶ X`. -/
def fromSpec₁ (c : TwoAffineOpenCover X) : Spec Γ(X, c.U₁) ⟶ X :=
  c.isAffine_U₁.fromSpec

/-- The open immersion `Spec Γ(X, U₂) ⟶ X`. -/
def fromSpec₂ (c : TwoAffineOpenCover X) : Spec Γ(X, c.U₂) ⟶ X :=
  c.isAffine_U₂.fromSpec

/-- The open immersion `Spec Γ(X, U₁ ⊓ U₂) ⟶ X`. -/
def fromSpecInf (c : TwoAffineOpenCover X) : Spec Γ(X, c.U₁ ⊓ c.U₂) ⟶ X :=
  c.isAffine_inf.fromSpec

/-- Restriction `Γ(X, U₁) →+* Γ(X, U₁ ⊓ U₂)`. -/
def restrict₁ (c : TwoAffineOpenCover X) : Γ(X, c.U₁) →+* Γ(X, c.U₁ ⊓ c.U₂) :=
  (X.presheaf.map (homOfLE (inf_le_left : c.U₁ ⊓ c.U₂ ≤ c.U₁)).op).hom

/-- Restriction `Γ(X, U₂) →+* Γ(X, U₁ ⊓ U₂)`. -/
def restrict₂ (c : TwoAffineOpenCover X) : Γ(X, c.U₂) →+* Γ(X, c.U₁ ⊓ c.U₂) :=
  (X.presheaf.map (homOfLE (inf_le_right : c.U₁ ⊓ c.U₂ ≤ c.U₂)).op).hom

/-- The two opens as a scheme-theoretic open cover of `X`. -/
def toOpenCover (c : TwoAffineOpenCover X) : X.OpenCover :=
  let U (i : Fin 2) := if i = 0 then c.U₁ else c.U₂
  Cover.mkOfCovers (Fin 2) (fun i ↦ (U i).toScheme) (fun i ↦ (U i).ι) sorry

end TwoAffineOpenCover

end AlgebraicGeometry.Scheme
