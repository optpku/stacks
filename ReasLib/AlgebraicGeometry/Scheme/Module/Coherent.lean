module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Monoidal.Category
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

/-!
# Coherent modules on locally Noetherian schemes

This leaf specializes the ringed-space notion of coherence to locally
Noetherian schemes and records its standard finite-presentation and
affine-sections criteria.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- On a locally Noetherian scheme, a module is coherent exactly when it is
quasi-coherent and of finite type. -/
@[stacks 01XZ]
theorem isCoherent_iff_isQuasicoherent_and_isFiniteType
    (ℱ : X.Modules) :
    ℱ.IsCoherent ↔ ℱ.IsQuasicoherent ∧ ℱ.IsFiniteType := sorry

/-- On a locally Noetherian scheme, coherence is equivalent to finite
presentation. -/
@[stacks 01XZ]
theorem isCoherent_iff_isFinitePresentation
    (ℱ : X.Modules) :
    ℱ.IsCoherent ↔ ℱ.IsFinitePresentation := sorry

/-- Coherence is equivalent to quasi-coherence together with finiteness of
sections on every affine open. -/
@[stacks 01XZ]
theorem isCoherent_iff_isQuasicoherent_and_forall_affineOpen_finite_sections
    (ℱ : X.Modules) :
    ℱ.IsCoherent ↔
      ℱ.IsQuasicoherent ∧
        ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(ℱ, U) := sorry

/-- A quasi-coherent module on a locally Noetherian scheme is coherent exactly when every
point has an affine open neighborhood on which the tilde comparison is an isomorphism
and the module of sections is finite over the ring of sections. -/
theorem isCoherent_iff_exists_affineOpen_isTilde_finite
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ℱ.IsCoherent ↔
      ∀ x : X, ∃ U : X.affineOpens,
        x ∈ (U : X.Opens) ∧
          IsIso (ℱ.restrict U.property.fromSpec).fromTildeΓ ∧
            Module.Finite Γ(X, (U : X.Opens)) Γ(ℱ, (U : X.Opens)) := sorry

namespace IsCoherent

/-- Coherence is equivalent to quasi-coherence together with finite sections
on an affine open cover. -/
@[stacks 01XZ]
theorem iff_exists_affineOpenCover
    (ℱ : X.Modules) :
    ℱ.IsCoherent ↔
      ℱ.IsQuasicoherent ∧
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀,
            Module.Finite
              Γ(X, 𝒰.openCover.f i |>.opensRange)
              Γ(ℱ, 𝒰.openCover.f i |>.opensRange) := sorry

end IsCoherent

/-- The structure module of a locally Noetherian scheme is coherent. -/
@[stacks 01XZ]
theorem structureSheaf_isCoherent
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent := sorry

/-- An invertible module on a locally Noetherian scheme is coherent. -/
@[stacks 01XZ]
theorem isCoherent_of_isInvertible
    (ℒ : X.Modules) [Invertible ℒ] :
    ℒ.IsCoherent := sorry

/-- Invertible modules on locally Noetherian schemes are canonically coherent. -/
instance instIsCoherentOfIsInvertible
    (ℒ : X.Modules) [Invertible ℒ] :
    ℒ.IsCoherent := sorry

/-- A finite locally free module on a locally Noetherian scheme is coherent. -/
@[stacks 01XZ]
theorem isCoherent_of_isFiniteLocallyFree
    (ℱ : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree ℱ] :
    ℱ.IsCoherent := sorry

/-- Finite locally free modules on a locally Noetherian scheme are canonically coherent. -/
instance instIsCoherentOfIsFiniteLocallyFree
    (ℱ : X.Modules) [SheafOfModules.IsFiniteLocallyFree ℱ] :
    ℱ.IsCoherent := sorry

/-- A module of fixed finite local rank on a locally Noetherian scheme is coherent. -/
theorem isCoherent_of_isFiniteLocallyFreeOfRank
    (r : ℕ) (ℱ : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    ℱ.IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
