/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Specialization.Sheaf
import StacksCheckRecall

/-! Separatedness and sheaf conditions for specialization presheaves. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Specialization

universe u

namespace AlgebraicGeometry.Scheme.Specialization

/- Remark 110.57.2 (1): the specialization-pair presheaf is separated for the étale topology. -/
@[stacks 05LF] #check (AlgebraicGeometry.Scheme.Specialization.pairPresheaf_isSeparated :
    Presheaf.IsSeparated etaleTopology pairPresheaf)

/- Remark 110.57.2 (2): every specialization-chain presheaf is separated for the étale topology. -/
@[stacks 05LF] #check (AlgebraicGeometry.Scheme.Specialization.chainPresheaf_isSeparated :
    ∀ n : ℕ, Presheaf.IsSeparated etaleTopology (chainPresheaf n))

/- Remark 110.57.2 (3): the specialization-pair presheaf is not an étale sheaf. -/
@[stacks 05LF] #check (AlgebraicGeometry.Scheme.Specialization.pairPresheaf_not_isSheaf :
    ¬ Presheaf.IsSheaf etaleTopology pairPresheaf)

/- Remark 110.57.2 (4): every positive-length specialization-chain presheaf fails to be an étale sheaf. -/
@[stacks 05LF] #check (AlgebraicGeometry.Scheme.Specialization.chainPresheaf_not_isSheaf :
    ∀ n : ℕ, 0 < n → ¬ Presheaf.IsSheaf etaleTopology (chainPresheaf n))

/- Remark 110.57.2 (5): the étale sheafification of the specialization-pair presheaf is a sheaf for the fppf topology. -/
@[stacks 05LF] #check (AlgebraicGeometry.Scheme.Specialization.pairSheaf_isSheaf_fppf :
    [HasWeakSheafify etaleTopology AddCommGrpCat.{u}] →
      Presheaf.IsSheaf fppfTopology pairSheaf.obj)

/- Remark 110.57.2 (6): the étale sheafification of every specialization-chain presheaf is a sheaf for the fppf topology. -/
@[stacks 05LF] #check (AlgebraicGeometry.Scheme.Specialization.chainSheaf_isSheaf_fppf :
    ∀ n : ℕ, [HasWeakSheafify etaleTopology AddCommGrpCat.{u}] →
      Presheaf.IsSheaf fppfTopology (chainSheaf n).obj)

end AlgebraicGeometry.Scheme.Specialization
