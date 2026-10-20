/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisModule
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.59.1: if `S = Spec K` for a field `K`, `s̄` is a geometric point of
`S`, and `G = Gal_κ(s)` is the absolute Galois group of the residue field, then
taking étale stalks `F ↦ F_s̄` is an equivalence
`Ab(S_étale) ≌ Mod_G` of abelian sheaves on the small étale site with discrete
continuous `G`-modules. -/
@[stacks 04JQ] #check (AlgebraicGeometry.Scheme.Etale.stalkGaloisModule_isEquivalence :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))),
    (stalkGaloisModule K s).IsEquivalence)

end AlgebraicGeometry.Scheme.Etale
