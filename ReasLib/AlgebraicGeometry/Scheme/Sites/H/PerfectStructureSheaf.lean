/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.PerfectStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FppfComparison
public import ReasLib.CategoryTheory.Sites.TopologyComparison.AbsoluteDerived
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Perfect structure sheaf and the h-to-fppf derived image

This module states the essential-image property of the perfect structure sheaf
on the big fppf site.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.H

/-- For a scheme of characteristic `p`, the perfect structure sheaf in degree zero
belongs to the essential image of the h-to-fppf right-derived direct image. -/
theorem perfStructureSheaf_mem_essImage
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    Functor.essImage
        (Absolute.rightDerived (AlgebraicGeometry.Scheme.H.fppf_le S))
        ((DerivedCategory.singleFunctor
            (SiteAbelianSheafCat (Scheme.fppfTopology.over S)) 0).obj
          (AlgebraicGeometry.Scheme.perfStructureSheaf p S)) :=
  sorry

end AlgebraicGeometry.Scheme.H

end
