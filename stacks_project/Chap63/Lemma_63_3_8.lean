/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 63.3.8: if `X` is proper over a field `k`, the compactly supported global
sections of an abelian étale sheaf `F` are all its global sections:
`H^0_c(X, F) = H^0(X, F)`. -/
@[stacks 0F73] #check
  (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupport_eq_univ :
    ∀ {k : Type u} [Field k] {X : SchemeOverField k} [IsProper X.hom]
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
      AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupport F = Set.univ)

end
