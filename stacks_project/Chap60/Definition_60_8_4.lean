/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Site


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme.Crystalline

variable (p : ℕ) [Fact p.Prime] (B : Base.{u} p)

/- Definition 60.8.4 (1) -/
@[stacks 07IB]
#check (AlgebraicGeometry.Scheme.Crystalline.CrystallineCovering
    B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed :
    ∀ (τ : AlgebraicGeometry.StandardTopology) {ι : Type v}
      {T : RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed}
      (family : ι → Over T), Prop)

/- Definition 60.8.4 (2) -/
@[stacks 07IB]
#check (AlgebraicGeometry.Scheme.Crystalline.crystallineZariskiTopology
    B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed :
    GrothendieckTopology
      (RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed))

/- Definition 60.8.4 (3) -/
@[stacks 07IB]
#check (AlgebraicGeometry.Scheme.Crystalline.bigCrystallineTopos
    B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed : Type (u + 2))

end AlgebraicGeometry.Scheme.Crystalline
