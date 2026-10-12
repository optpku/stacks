/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support

/-!
# Scheme-theoretic support of a module sheaf

This leaf owns the scheme-level interface identifying ideal-sheaf data with
the annihilator-defined closed subscheme associated to a finite-type
quasi-coherent module sheaf.  The underlying point-set support remains the
ringed-space module-support owner.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules)

/-- The ideal-sheaf datum obtained from the annihilators of the modules of sections of `ℱ`
on affine opens. -/
def schemeTheoreticSupport : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦
    Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1))

/-- Ideal-sheaf data `I` is a scheme-theoretic support of `ℱ` when its ideal on each affine
open is the annihilator of the corresponding module of sections. -/
@[stacks 05JV]
def IsSchemeTheoreticSupport (I : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1))

/-- The affine-open annihilator characterization of scheme-theoretic support. -/
@[stacks 05JV]
theorem isSchemeTheoreticSupport_iff (I : X.IdealSheafData) :
    IsSchemeTheoreticSupport ℱ I ↔
      ∀ U : X.affineOpens, I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1)) := sorry

/-- On every affine open, the ideal of the scheme-theoretic support is the annihilator of
the corresponding module of sections. -/
theorem schemeTheoreticSupport_ideal [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (U : X.affineOpens) :
    (schemeTheoreticSupport ℱ).ideal U =
      Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1)) := sorry

/-- An ideal-sheaf datum is a scheme-theoretic support exactly when it is the canonical
scheme-theoretic support. -/
theorem isSchemeTheoreticSupport_iff_eq_schemeTheoreticSupport
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (I : X.IdealSheafData) :
    IsSchemeTheoreticSupport ℱ I ↔ I = schemeTheoreticSupport ℱ := sorry

/-- The canonical scheme-theoretic support has the affine annihilator characterization. -/
theorem schemeTheoreticSupport_isSchemeTheoreticSupport
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    IsSchemeTheoreticSupport ℱ (schemeTheoreticSupport ℱ) := sorry

/-- The ordinary module support is the underlying closed set of its scheme-theoretic support. -/
@[stacks 05JV]
theorem moduleSupport_eq_of_isSchemeTheoreticSupport
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (I : X.IdealSheafData) (hI : IsSchemeTheoreticSupport ℱ I) :
    RingedSpace.moduleSupport ℱ = (I.support : Set X) := sorry

/-- A quasicoherent module on the subscheme cut out by `J` pushes forward to `ℱ` exactly
when `J` is at most the canonical scheme-theoretic support. -/
theorem exists_pushforward_iff_le_schemeTheoreticSupport
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (J : X.IdealSheafData) :
    (∃ 𝒢 : J.subscheme.Modules,
      ∃ _ : 𝒢.IsQuasicoherent,
        Nonempty ((Scheme.Modules.pushforward J.subschemeι).obj 𝒢 ≅ ℱ)) ↔
      J ≤ schemeTheoreticSupport ℱ := sorry

/-- The canonical scheme-theoretic support has the affine annihilator characterization and
is the least closed subscheme from which `ℱ` is the pushforward of a quasicoherent module. -/
theorem schemeTheoreticSupport_spec [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    IsSchemeTheoreticSupport ℱ (schemeTheoreticSupport ℱ) ∧
      ∀ J : X.IdealSheafData,
        (∃ 𝒢 : J.subscheme.Modules,
          ∃ _ : 𝒢.IsQuasicoherent,
            Nonempty ((Scheme.Modules.pushforward J.subschemeι).obj 𝒢 ≅ ℱ)) ↔
          J ≤ schemeTheoreticSupport ℱ := sorry

/-- A finite-type quasicoherent module descends to a finite-type quasicoherent module of full
support on any ideal-sheaf datum having its affine annihilator characterization. -/
theorem exists_finiteType_module_of_isSchemeTheoreticSupport
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (I : X.IdealSheafData) (hI : IsSchemeTheoreticSupport ℱ I) :
    ∃ 𝒢 : I.subscheme.Modules,
      ∃ _ : 𝒢.IsQuasicoherent,
        ∃ _ : 𝒢.IsFiniteType,
          Nonempty ((Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ) ∧
            RingedSpace.moduleSupport 𝒢 = Set.univ := sorry

/-- Two modules on the same closed subscheme with chosen pushforward identifications admit a
unique isomorphism compatible with those identifications. -/
theorem existsUnique_iso_of_pushforward_iso
    (I : X.IdealSheafData) (𝒢 𝒢' : I.subscheme.Modules)
    (e : (Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ)
    (e' : (Scheme.Modules.pushforward I.subschemeι).obj 𝒢' ≅ ℱ) :
    ∃! α : 𝒢 ≅ 𝒢',
      ((Scheme.Modules.pushforward I.subschemeι).mapIso α).trans e' = e := sorry

end Scheme.Modules
end AlgebraicGeometry
