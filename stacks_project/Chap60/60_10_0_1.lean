/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline

universe u

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)

/- 60.10.0.1 (1): a morphism in the big crystalline site induces the comparison
from the inverse image of the target restriction to the source restriction. -/
@[stacks 07IP] #check (AlgebraicGeometry.Scheme.Crystalline.Sheaf.comparison :
  ∀ (F : CategoryTheory.Sheaf
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed) (Type u))
    {T T' : RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed} (f : T ⟶ T'),
    (TopCat.Sheaf.pullback (Type u) f.thickening.base).obj (Sheaf.restrictObj F T') ⟶
      Sheaf.restrictObj F T)

/- 60.10.0.1 (2): a morphism in the small crystalline site induces the comparison
from the inverse image of the target restriction to the source restriction. -/
@[stacks 07IP] #check (AlgebraicGeometry.Scheme.Crystalline.Sheaf.smallComparison :
  ∀ (F : CategoryTheory.Sheaf
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) (Type u))
    {T T' : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed} (f : T ⟶ T'),
    (TopCat.Sheaf.pullback (Type u) f.hom.thickening.base).obj (Sheaf.smallRestrictObj F T') ⟶
      Sheaf.smallRestrictObj F T)
