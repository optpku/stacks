/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.PerfectStructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived

noncomputable section

universe u

/- Lemma 59.107.1: if `p` is prime and `S` is a scheme of characteristic `p`,
then the perfect structure sheaf on the big fppf site over `S`, placed in degree
zero, belongs to the essential image of the h-to-fppf right-derived direct image. -/
@[stacks 0EWT] #check
  (AlgebraicGeometry.Scheme.H.perfStructureSheaf_mem_essImage :
    ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p],
      Functor.essImage
        (Absolute.rightDerived (AlgebraicGeometry.Scheme.H.fppf_le S))
        ((DerivedCategory.singleFunctor
            (SiteAbelianSheafCat (Scheme.fppfTopology.over S)) 0).obj
          (AlgebraicGeometry.Scheme.perfStructureSheaf p S)))

end

end
