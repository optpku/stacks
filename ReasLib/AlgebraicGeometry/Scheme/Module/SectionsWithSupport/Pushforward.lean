module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionsWithSupport

/-!
# Pushforward of sections with support

This file records compatibility between pushforward of module sheaves and sections supported in a
closed subset.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open SheafOfModules.ClosedSubset.SectionsWithSupport

/-- For a quasi-compact and quasi-separated morphism of schemes, pushforward carries the
subsheaf of sections supported in the inverse image of a closed subset to the subsheaf of
sections supported in that closed subset, sectionwise on every open, provided its complement is
retrocompact. -/
theorem range_pushforward_sectionsWithSupportInι_app_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (Z : TopologicalSpace.Closeds Y)
    (hretro : IsRetrocompact ((openComplement Z : Y.Opens) : Set Y))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : Y.Opens) :
    Set.range (((pushforward f).map
        (sectionsWithSupportInι (Z.preimage f.continuous) ℱ)).app U) =
      Set.range ((sectionsWithSupportInι Z ((pushforward f).obj ℱ)).app U) := sorry

end AlgebraicGeometry.Scheme.Modules
