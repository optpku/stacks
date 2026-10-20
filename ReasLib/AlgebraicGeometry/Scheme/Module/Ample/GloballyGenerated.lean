module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated

/-!
# Ample Invertible Modules from Globally Generated Modules

This file gives a criterion for the existence of an ample invertible module in terms of affine
nonvanishing neighborhoods from globally generated invertible modules.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-compact scheme has an ample invertible module if every point has an affine
nonvanishing neighborhood cut out by a section of a globally generated invertible module. -/
theorem hasAmpleInvertibleModule_of_globallyGenerated_affineNonvanishingCover
    {X : Scheme.{u}} [CompactSpace X]
    (h : ∀ x : X, ∃ (L : X.Modules) (hL : Invertible L),
      SheafOfModules.IsGloballyGenerated L ∧
        ∃ s : Γ(L, ⊤), AffineOpenNeighborhood x (hL.sectionNonvanishingOpen s)) :
    HasAmpleInvertibleModule X := sorry

end AlgebraicGeometry.Scheme.Modules
