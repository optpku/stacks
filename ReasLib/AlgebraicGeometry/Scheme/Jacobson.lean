module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Locality
public import ReasLib.RingTheory.LocalProperty.Jacobson

/-!
# Jacobson Schemes

This file characterizes Jacobson schemes using affine section rings and open covers, and records
preservation under restriction to open subschemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- Every open subscheme of a Jacobson scheme is Jacobson. -/
theorem jacobsonSpace_toScheme (hX : JacobsonSpace X) (U : X.Opens) :
    JacobsonSpace U.toScheme := sorry

/-- A scheme is Jacobson exactly when every affine-open section ring is Jacobson. -/
theorem jacobsonSpace_iff_forall_affineOpen :
    JacobsonSpace X ↔
      ∀ U : X.affineOpens, IsJacobsonRing Γ(X, U) := sorry

/-- A scheme is Jacobson exactly when the Jacobson-ring property holds locally on affine
neighbourhoods. -/
theorem jacobsonSpace_iff_hasRingPropertyLocally :
    JacobsonSpace X ↔
      X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsJacobsonRing A) := sorry

/-- A Jacobson scheme canonically has the Jacobson-ring property locally on affine
neighbourhoods. -/
instance instHasRingPropertyLocallyIsJacobsonRingOfJacobsonSpace [JacobsonSpace X] :
    X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsJacobsonRing A) := sorry

/-- A scheme is Jacobson exactly when one affine open cover has Jacobson section rings. -/
theorem jacobsonSpace_iff_exists_affineOpenCover :
    JacobsonSpace X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsJacobsonRing Γ(X, (𝒰.f i).opensRange) := sorry

/-- A scheme is Jacobson exactly when it has an open cover by Jacobson open subschemes. -/
theorem jacobsonSpace_iff_exists_openCover :
    JacobsonSpace X ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, JacobsonSpace ((𝒰.f i).opensRange).toScheme := sorry

/-- Jacobsonness, local Jacobsonness, affine-open Jacobsonness, and the corresponding affine and
open cover criteria are equivalent. -/
theorem jacobsonSpace_tfae :
    List.TFAE [
      JacobsonSpace X,
      X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsJacobsonRing A),
      ∀ U : X.affineOpens, IsJacobsonRing Γ(X, U),
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsJacobsonRing Γ(X, (𝒰.f i).opensRange),
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, JacobsonSpace ((𝒰.f i).opensRange).toScheme] := sorry

end AlgebraicGeometry.Scheme
