/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Theorem_59_56_3_StalkFunctor

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Theorem 59.56.3: if `S = Spec K` for a field `K`, `s̄` is a geometric point
of `S`, and `G = Gal_κ(s)` is the absolute Galois group of the residue field,
then taking étale stalks `F ↦ F_s̄` is an equivalence
`Sh(S_étale) ≌ G-Sets` of sheaves on the small étale site with discrete
continuous `G`-sets. -/
@[stacks 03QT]
instance stalkGaloisSet_isEquivalence
    (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    (stalkGaloisSet K s).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.Etale
