/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.PolynomialLaw.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Norms on Picard groups of schemes

This file owns affine-local norm data for a finite morphism and the induced norm homomorphism on
Picard groups.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ)

/-- The section ring on the inverse image of an open set is an algebra over the section ring on
that open set via the morphism of schemes. -/
instance normPullbackSectionAlgebra (U : Y.Opens) :
    Algebra (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U)) :=
  (π.app U).hom.toAlgebra

/-- A multiplicative norm on the structure sheaves, without polynomial-law data. -/
structure OrdinaryFiniteMorphismNorm (π : X ⟶ Y) where
  /-- The multiplicative map from the pushed-forward structure sheaf. -/
  norm :
    ((TopCat.Presheaf.pushforward CommRingCat π.base).obj X.presheaf ⋙
      forget₂ CommRingCat CommMonCat) ⟶
        (Y.presheaf ⋙ forget₂ CommRingCat CommMonCat)

namespace OrdinaryFiniteMorphismNorm

variable {π : X ⟶ Y}

/-- The norm on sections over an open set. -/
def app (N : OrdinaryFiniteMorphismNorm π) (U : Y.Opens) :
    Γ(X, π ⁻¹ᵁ U) →* Γ(Y, U) :=
  (N.norm.app (op U)).hom

/-- The norm takes pulled-back sections to their `d`th powers. -/
def HasDegree (N : OrdinaryFiniteMorphismNorm π) (d : ℕ) : Prop :=
  ∀ (U : Y.Opens) (r : Γ(Y, U)), N.app U (π.app U r) = r ^ d

/-- Vanishing at a source point implies vanishing at its image. -/
def PreservesZeroLocus (N : OrdinaryFiniteMorphismNorm π) : Prop :=
  ∀ (U : Y.Opens) (x : X) (hx : x ∈ π ⁻¹ᵁ U) (s : Γ(X, π ⁻¹ᵁ U)),
    X.residue x (X.presheaf.germ (π ⁻¹ᵁ U) x hx s) = 0 →
      Y.residue (π.base x) (Y.presheaf.germ U (π.base x) hx (N.app U s)) = 0

end OrdinaryFiniteMorphismNorm

/-- The defining conditions for an ordinary norm of degree `d`. -/
def IsOrdinaryFiniteMorphismNorm (π : X ⟶ Y) (d : ℕ)
    (N : OrdinaryFiniteMorphismNorm π) : Prop :=
  1 ≤ d ∧ N.HasDegree d ∧ N.PreservesZeroLocus

/-- A finite-morphism norm consists of a multiplicative morphism from the pushed-forward
structure presheaf to the target structure presheaf, together with compatible polynomial laws
on affine sections whose scalar extensions remain multiplicative. -/
structure FiniteMorphismNorm (π : X ⟶ Y) where
  /-- The multiplicative norm morphism on structure presheaves. -/
  norm :
    ((TopCat.Presheaf.pushforward CommRingCat π.base).obj X.presheaf ⋙
      forget₂ CommRingCat CommMonCat) ⟶
        (Y.presheaf ⋙ forget₂ CommRingCat CommMonCat)
  /-- The polynomial law inducing the norm on the sections of each affine open. -/
  polynomialLaw : ∀ (U : Y.Opens) (_ : IsAffineOpen U),
    Γ(X, π ⁻¹ᵁ U) →ₚₗ[Γ(Y, U)] Γ(Y, U)
  /-- On the ground ring, the affine polynomial law agrees with the presheaf norm. -/
  ground_eq_app : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (x : Γ(X, π ⁻¹ᵁ U)),
    (polynomialLaw U hU).ground x = norm.app (op U) x
  /-- Every scalar extension of an affine polynomial law sends one to one. -/
  baseChange_one : ∀ (U : Y.Opens) (hU : IsAffineOpen U)
      (S : Type*) [CommRing S] [Algebra (Γ(Y, U)) S],
    Algebra.TensorProduct.rid (Γ(Y, U)) S S
        ((polynomialLaw U hU).toFun S 1) = 1
  /-- Every scalar extension of an affine polynomial law preserves multiplication. -/
  baseChange_mul : ∀ (U : Y.Opens) (hU : IsAffineOpen U)
      (S : Type*) [CommRing S] [Algebra (Γ(Y, U)) S]
      (x y : S ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U)),
    Algebra.TensorProduct.rid (Γ(Y, U)) S S
        ((polynomialLaw U hU).toFun S (x * y)) =
      Algebra.TensorProduct.rid (Γ(Y, U)) S S
          ((polynomialLaw U hU).toFun S x) *
        Algebra.TensorProduct.rid (Γ(Y, U)) S S
          ((polynomialLaw U hU).toFun S y)

namespace FiniteMorphismNorm

variable {π : X ⟶ Y}

/-- Forget the polynomial laws and retain the multiplicative sheaf norm. -/
def toOrdinary (N : FiniteMorphismNorm π) : OrdinaryFiniteMorphismNorm π :=
  ⟨N.norm⟩

/-- The multiplicative norm map on sections over an open set. -/
def app (N : FiniteMorphismNorm π) (U : Y.Opens) :
    Γ(X, π ⁻¹ᵁ U) →* Γ(Y, U) :=
  (N.norm.app (op U)).hom

/-- The norm on affine sections after extension to a commutative scalar algebra. -/
def baseChange (N : FiniteMorphismNorm π) (U : Y.Opens) (hU : IsAffineOpen U)
    (S : Type*) [CommRing S] [Algebra (Γ(Y, U)) S] :
    (S ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U)) →* S where
  toFun x := Algebra.TensorProduct.rid (Γ(Y, U)) S S ((N.polynomialLaw U hU).toFun S x)
  map_one' := N.baseChange_one U hU S
  map_mul' := N.baseChange_mul U hU S

/-- A norm has degree `d` when it sends every pulled-back base section to its `d`th power. -/
def HasDegree (N : FiniteMorphismNorm π) (d : ℕ) : Prop :=
  ∀ (U : Y.Opens) (r : Γ(Y, U)), N.app U (π.app U r) = r ^ d

/-- A norm preserves zero loci when residue-field vanishing at a source point implies
residue-field vanishing of the norm at its image. -/
def PreservesZeroLocus (N : FiniteMorphismNorm π) : Prop :=
  ∀ (U : Y.Opens) (x : X) (hx : x ∈ π ⁻¹ᵁ U) (s : Γ(X, π ⁻¹ᵁ U)),
    X.residue x (X.presheaf.germ (π ⁻¹ᵁ U) x hx s) = 0 →
      Y.residue (π.base x) (Y.presheaf.germ U (π.base x) hx (N.app U s)) = 0

end FiniteMorphismNorm

/-- A finite-morphism norm of positive degree `d` satisfies the power formula on base sections
and preserves residue-field zero loci. -/
def IsFiniteMorphismNorm (π : X ⟶ Y) (d : ℕ) (N : FiniteMorphismNorm π) : Prop :=
  1 ≤ d ∧ N.HasDegree d ∧ N.PreservesZeroLocus

/-- Forgetting polynomial laws preserves all the ordinary norm conditions. -/
theorem FiniteMorphismNorm.toOrdinary_isNorm (N : FiniteMorphismNorm π)
    (hN : IsFiniteMorphismNorm π d N) : IsOrdinaryFiniteMorphismNorm π d N.toOrdinary :=
  hN

/-- A finite-morphism norm satisfies the defining norm conditions exactly when its degree is
positive, it has the required power formula, and it preserves residue-field zero loci. -/
theorem isFiniteMorphismNorm_iff (N : FiniteMorphismNorm π) :
    IsFiniteMorphismNorm π d N ↔
      1 ≤ d ∧ N.HasDegree d ∧ N.PreservesZeroLocus := sorry

/-- A degree-`d` norm for a finite morphism `π : X ⟶ Y` induces a homomorphism
`Pic(X) → Pic(Y)` taking the pullback of an invertible module to its `d`-fold tensor-power
class. The intended construction applies the sheaf norm to transition functions on opens
over which the invertible module trivializes after pullback. -/
@[stacks 0BCY]
theorem exists_picardNorm_of_exists_norm
    [IsFinite π]
    (hnorm : ∃ N : OrdinaryFiniteMorphismNorm π, IsOrdinaryFiniteMorphismNorm π d N) :
    ∃ normπ : X.PicardGroup →+ Y.PicardGroup,
      ∀ (𝒩 : Y.Modules) [MonoidalCategory.isInvertibleObject 𝒩],
        normπ (Scheme.Hom.picardPullbackClass π 𝒩) =
          d • Scheme.Modules.picardClass 𝒩 := sorry

end AlgebraicGeometry.Scheme
