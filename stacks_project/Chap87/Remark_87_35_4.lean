/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Padic

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.AffineFormalAlgebraicSpace

/- Remark 87.35.4
Even if the structure sheaf 𝒪_X has good properties, this does not yield a
good theory of quasi-coherent modules. For example, Examples 110.13 shows that
the most natural QCoh category on a Noetherian affine formal algebraic space
need not be abelian; the witness is Spf(ℤ_[p]), the fppf sheaf colimit of
p-adic thickenings.
-/
@[stacks 0DEM] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.not_abelian :
    ∀ (p : ℕ) [Fact p.Prime],
      ¬ Nonempty (Abelian (QCoh (GroupoidsOver.ofPresheaf (padicSpectrum p).obj))))
