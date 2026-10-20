/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fpqc.Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

/- The canonical Zariski topology is coarser than the fpqc topology. -/
#check
  (AlgebraicGeometry.Scheme.zariskiTopology_le_fpqcTopology :
    zariskiTopology ≤ fpqcTopology)

/- Remark 59.15.9 (1): the fpqc topology is finer than the etale topology. -/
@[stacks 03O4] #check
  (AlgebraicGeometry.Scheme.etaleTopology_le_fpqcTopology :
    etaleTopology ≤ fpqcTopology)

/- Remark 59.15.9 (2): the fpqc topology is finer than the smooth topology. -/
@[stacks 03O4] #check
  (AlgebraicGeometry.Scheme.bigSmoothSite_le_fpqcTopology :
    bigSmoothSite ≤ fpqcTopology)

/- Remark 59.15.9 (3): the fpqc topology is finer than the syntomic topology. -/
@[stacks 03O4] #check
  (AlgebraicGeometry.Scheme.bigSyntomicSite_le_fpqcTopology :
    bigSyntomicSite ≤ fpqcTopology)

/- The canonical fppf topology is coarser than the fpqc topology. -/
#check
  (AlgebraicGeometry.Scheme.fppfTopology_le_fpqcTopology :
    fppfTopology ≤ fpqcTopology)

/- Remark 59.15.9 (4): a presheaf satisfying the fpqc sheaf condition satisfies the
sheaf condition for every Grothendieck topology `J` with `J ≤ fpqcTopology`. -/
@[stacks 03O4] #check
  (AlgebraicGeometry.Scheme.isSheaf_of_fpqc_of_le :
    ∀ (S : Scheme.{u}) {J : GrothendieckTopology Scheme.{u}}
      (F : (Over S)ᵒᵖ ⥤ Type v),
      J ≤ fpqcTopology → Presieve.IsSheaf (fpqcTopology.over S) F →
        Presieve.IsSheaf (J.over S) F)

/- Remark 59.15.9 (5): every representable presheaf is a sheaf on the etale site of a scheme. -/
@[stacks 03O4] #check
  (AlgebraicGeometry.Scheme.isSheaf_etale_of_isRepresentable :
    ∀ (S : Scheme.{u}) (P : (Over S)ᵒᵖ ⥤ Type v) [P.IsRepresentable],
      Presieve.IsSheaf (etaleTopology.over S) P)

end AlgebraicGeometry.Scheme
