module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionsWithSupport.Pushforward
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

open SheafOfModules.ClosedSubset.SectionsWithSupport
open AlgebraicGeometry.Scheme.Modules

/-
Lemma 28.24.7: for a quasi-compact and quasi-separated morphism `f : X ⟶ Y`, the pushforward
of the subsheaf of `ℱ` supported in `f ⁻¹' Z` is, sectionwise on every open of `Y`, the subsheaf
of `f_* ℱ` supported in `Z`.
-/
@[stacks 07ZQ] #check
  (AlgebraicGeometry.Scheme.Modules.range_pushforward_sectionsWithSupportInι_app_eq :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      (Z : TopologicalSpace.Closeds Y)
      (hretro : IsRetrocompact ((openComplement Z : Y.Opens) : Set Y))
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (U : Y.Opens),
      Set.range (((pushforward f).map
          (sectionsWithSupportInι (Z.preimage f.continuous) ℱ)).app U) =
        Set.range ((sectionsWithSupportInι Z ((pushforward f).obj ℱ)).app U))
