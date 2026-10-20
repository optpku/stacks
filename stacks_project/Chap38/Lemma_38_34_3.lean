/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Submersive

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 38.34.3: for a finite family of finite type morphisms to a Noetherian
scheme, the coproduct morphism is universally submersive if and only if the
family is an h covering. -/
@[stacks 0ETT] #check
  (AlgebraicGeometry.Scheme.universallySubmersive_sigmaDesc_iff_hCovering :
    ∀ {X : Scheme.{u}} {ι : Type u} [Finite ι] [IsNoetherian X]
      (family : ι → Over X) [∀ i, Scheme.Hom.FiniteType (family i).hom],
      UniversallySubmersive (Limits.Sigma.desc (fun i ↦ (family i).hom)) ↔
        HCovering family)

end AlgebraicGeometry.Scheme
