/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_59_1_StalkFunctor

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 59.59.1: if `S = Spec K` for a field `K`, `s̄` is a geometric point of
`S`, and `G = Gal_κ(s)` is the absolute Galois group of the residue field, then
taking étale stalks `F ↦ F_s̄` is an equivalence
`Ab(S_étale) ≌ Mod_G` of abelian sheaves on the small étale site with discrete
continuous `G`-modules. -/
@[stacks 04JQ]
instance stalkGaloisModule_isEquivalence
    (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    (stalkGaloisModule K s).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.Etale
