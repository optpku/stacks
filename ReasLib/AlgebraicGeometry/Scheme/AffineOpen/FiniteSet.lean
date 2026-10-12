/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-!
# Affine open neighborhoods of finite subsets

Sufficient conditions for a finite subset of a scheme to lie in a single affine open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- A finite subset of a scheme immersed in a projective spectrum is contained in a single
affine open. -/
theorem exists_affineOpen_containing_finiteSet_of_isImmersion_to_Proj
    {X : Scheme.{u}} {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (i : X ⟶ Proj 𝒜) [IsImmersion i] (E : Set X) (hE : E.Finite) :
    ∃ U : X.affineOpens, E ⊆ ((U : X.Opens) : Set X) := sorry

/-- A finite subset of a scheme immersed in an affine scheme is contained in a single affine
open. -/
theorem exists_affineOpen_containing_finiteSet_of_isImmersion_to_isAffine
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsAffine Y] [IsImmersion i]
    (E : Set X) (hE : E.Finite) :
    ∃ U : X.affineOpens, E ⊆ ((U : X.Opens) : Set X) := sorry

/-- A finite subset of a quasi-affine scheme is contained in a single affine open. -/
theorem exists_affineOpen_containing_finiteSet_of_isQuasiAffine
    {X : Scheme.{u}} [X.IsQuasiAffine] (E : Set X) (hE : E.Finite) :
    ∃ U : X.affineOpens, E ⊆ ((U : X.Opens) : Set X) := sorry

/-- A finite subset of a scheme admitting an ample invertible module is contained in a single
affine open. -/
theorem exists_affineOpen_containing_finiteSet_of_hasAmpleInvertibleModule
    {X : Scheme.{u}} (hX : Scheme.Modules.HasAmpleInvertibleModule X)
    (E : Set X) (hE : E.Finite) :
    ∃ U : X.affineOpens, E ⊆ ((U : X.Opens) : Set X) := sorry

/-- A finite subset of a quasi-affine scheme, a scheme immersed in an affine scheme, a scheme
admitting an ample invertible module, or a scheme immersed in a projective spectrum is contained
in a single affine open. -/
theorem exists_affineOpen_containing_finiteSet
    {X : Scheme.{u}}
    (hX :
      X.IsQuasiAffine ∨
        (∃ (Y : Scheme.{u}) (i : X ⟶ Y), IsAffine Y ∧ IsImmersion i) ∨
        Scheme.Modules.HasAmpleInvertibleModule X ∨
        ∃ (A : Type u) (σ : Type v) (_ : CommRing A) (_ : SetLike σ A)
          (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
          (i : X ⟶ Proj 𝒜), IsImmersion i)
    (E : Set X) (hE : E.Finite) :
    ∃ U : X.affineOpens, E ⊆ ((U : X.Opens) : Set X) := sorry

end AlgebraicGeometry.Scheme
