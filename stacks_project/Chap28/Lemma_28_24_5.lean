module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionsWithSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable (Z : TopologicalSpace.Closeds X) (ℱ : X.Modules) (U : X.Opens)

/- The sheaf of sections supported in a closed subset is the kernel of restriction to its open
complement. -/
#check (AlgebraicGeometry.Scheme.Modules.sectionsWithSupportIn Z ℱ : X.Modules)

/- Its canonical map to the original module sheaf is the kernel inclusion. -/
#check (AlgebraicGeometry.Scheme.Modules.sectionsWithSupportInι Z ℱ :
  AlgebraicGeometry.Scheme.Modules.sectionsWithSupportIn Z ℱ ⟶ ℱ)

/- On each open, the range of the kernel inclusion is exactly the set of sections whose support
is contained in the closed subset. -/
#check
  (SheafOfModules.ClosedSubset.SectionsWithSupport.inclusion_app_range
    X.ringCatSheaf Z ℱ U :
    Set.range ((AlgebraicGeometry.Scheme.Modules.sectionsWithSupportInι Z ℱ).app U) =
      { s : Γ(ℱ, U) |
        SheafOfModules.localSectionSupport s ⊆ { x : U | x.1 ∈ (Z : Set X) } })

/- Lemma 28.24.5 (1): if the open complement of `Z` is retrocompact, then every affine open
admits a finitely generated ideal cutting out its intersection with `Z`. -/
@[stacks 07ZP]
#check
  (AlgebraicGeometry.Scheme.Modules.exists_fg_ideal_of_isRetrocompact_openComplement :
    ∀ {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X),
      IsRetrocompact
          (SheafOfModules.ClosedSubset.SectionsWithSupport.openComplement Z : Set X) →
        ∀ U : X.affineOpens,
          ∃ I : Ideal Γ(X, U.1), I.FG ∧
            ((Z : Set X) ∩ (U.1 : Set X) =
              X.zeroLocus (I : Set Γ(X, U.1)) ∩ (U.1 : Set X)))

/- Lemma 28.24.5 (2): on an affine open cut out by a finitely generated ideal `I`, the supported
sections are exactly the sections annihilated by some power of `I`. -/
@[stacks 07ZP]
#check
  (AlgebraicGeometry.Scheme.Modules.range_sectionsWithSupportInι_app_eq_affine_idealPowerTorsion :
    ∀ {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (U : X.affineOpens) (I : Ideal Γ(X, U.1)), I.FG →
        ((Z : Set X) ∩ (U.1 : Set X) =
          X.zeroLocus (I : Set Γ(X, U.1)) ∩ (U.1 : Set X)) →
        Set.range ((AlgebraicGeometry.Scheme.Modules.sectionsWithSupportInι Z ℱ).app U.1) =
          { x : Γ(ℱ, U.1) |
            ∃ n : ℕ, ∀ a : Γ(X, U.1),
              a ∈ (I ^ n : Ideal Γ(X, U.1)) → a • x = 0 })

/- Lemma 28.24.5 (3): under the same retrocompactness hypothesis, the sheaf of supported sections
of a quasicoherent module sheaf is quasicoherent. -/
@[stacks 07ZP]
#check
  (AlgebraicGeometry.Scheme.Modules.sectionsWithSupportIn_isQuasicoherent :
    ∀ {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X),
      IsRetrocompact
          (SheafOfModules.ClosedSubset.SectionsWithSupport.openComplement Z : Set X) →
        ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent],
          (AlgebraicGeometry.Scheme.Modules.sectionsWithSupportIn Z ℱ).IsQuasicoherent)

end AlgebraicGeometry.Scheme.Modules
