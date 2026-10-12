/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.SectionsWithSupport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Retrocompact
public import ReasLib.RingTheory.Module.Support.IdealPower
public import ReasLib.RingTheory.Support.Cyclic

/-!
# Sections with support in a closed subset

This file specializes the closed-support kernel of a sheaf of modules to schemes and records its
affine ideal-power description and quasicoherence.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

open SheafOfModules.ClosedSubset.SectionsWithSupport

/-- The module sheaf of sections of `ℱ` whose restriction to the open complement of `Z`
vanishes. -/
abbrev sectionsWithSupportIn (Z : TopologicalSpace.Closeds X) (ℱ : X.Modules) : X.Modules :=
  object X.ringCatSheaf Z ℱ

/-- The canonical inclusion of sections supported in `Z` into the ambient module sheaf. -/
abbrev sectionsWithSupportInι (Z : TopologicalSpace.Closeds X) (ℱ : X.Modules) :
    sectionsWithSupportIn Z ℱ ⟶ ℱ :=
  inclusion X.ringCatSheaf Z ℱ

/-- If the open complement of `Z` is retrocompact, every affine open of `X` admits a finitely
generated ideal cutting out its intersection with `Z`. -/
theorem exists_fg_ideal_of_isRetrocompact_openComplement
    (Z : TopologicalSpace.Closeds X)
    (hretro : IsRetrocompact (openComplement Z : Set X))
    (U : X.affineOpens) :
    ∃ I : Ideal Γ(X, U.1), I.FG ∧
      ((Z : Set X) ∩ (U.1 : Set X) =
        X.zeroLocus (I : Set Γ(X, U.1)) ∩ (U.1 : Set X)) := sorry

/-- On an affine open where `Z` is cut out by a finitely generated ideal `I`, the image of the
closed-support inclusion consists exactly of the sections annihilated by some power of `I`. -/
theorem range_sectionsWithSupportInι_app_eq_affine_idealPowerTorsion
    (Z : TopologicalSpace.Closeds X)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : X.affineOpens)
    (I : Ideal Γ(X, U.1))
    (hIfg : I.FG)
    (hI : (Z : Set X) ∩ (U.1 : Set X) =
      X.zeroLocus (I : Set Γ(X, U.1)) ∩ (U.1 : Set X)) :
    Set.range ((sectionsWithSupportInι Z ℱ).app U.1) =
      {x : Γ(ℱ, U.1) |
        ∃ n : ℕ, ∀ a : Γ(X, U.1), a ∈ (I ^ n : Ideal Γ(X, U.1)) → a • x = 0} := sorry

/-- If the open complement of `Z` is retrocompact, the subsheaf of a quasicoherent module sheaf
whose sections are supported in `Z` is quasicoherent. -/
theorem sectionsWithSupportIn_isQuasicoherent
    (Z : TopologicalSpace.Closeds X)
    (hretro : IsRetrocompact (openComplement Z : Set X))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (sectionsWithSupportIn Z ℱ).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Modules
