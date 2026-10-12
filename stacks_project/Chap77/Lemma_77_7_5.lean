/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# Lemma 77.7.5

In Situation 77.7.1, an exact sequence `ℱ ⟶ 𝒢 ⟶ ℋ ⟶ 0` of quasi-coherent modules
identifies the isomorphism functor of `v` with the vanishing functor of `u`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 ℋ : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] [ℋ.IsQuasicoherent]

/-- Lemma 77.7.5: In Situation 77.7.1, given an exact sequence `ℱ ⟶ 𝒢 ⟶ ℋ ⟶ 0` of
quasi-coherent modules on `X`, the subterminal functors satisfy `F_{v,iso} = F_{u,zero}`:
for every scheme `T` over `B`, `baseChangeMap f T.hom v` is an isomorphism if and only if
`baseChangeMap f T.hom u` is zero. -/
@[stacks 0CVM]
theorem baseChangeMap_isIso_iff_zero_of_exact (u : ℱ ⟶ 𝒢) (v : 𝒢 ⟶ ℋ)
    (h_comp : u ≫ v = 0) (h_exact : (ShortComplex.mk u v h_comp).Exact)
    [Epi v] (T : SchemeOver B) :
    IsIso (baseChangeMap f T.hom v) ↔ baseChangeMap f T.hom u = 0 :=
  sorry

/-- Pointwise, `isomorphismFunctor f v` is nonempty on an object `T` of `SchemeOver B`
if and only if `baseChangeMap f T.hom u` vanishes, under the exactness hypotheses of
`baseChangeMap_isIso_iff_zero_of_exact`. -/
theorem isomorphismFunctor_obj_nonempty_iff_zero_of_exact (u : ℱ ⟶ 𝒢) (v : 𝒢 ⟶ ℋ)
    (h_comp : u ≫ v = 0) (h_exact : (ShortComplex.mk u v h_comp).Exact)
    [Epi v] (T : SchemeOver B) :
    Nonempty ((isomorphismFunctor f v).obj (op T)) ↔ baseChangeMap f T.hom u = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
