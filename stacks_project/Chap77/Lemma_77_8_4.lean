/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap71.Lemma_71_15_2_Fiber
public import stacks_project.Chap77.«77_7_1_1_BaseChange»

/-!
# Vanishing of a fibre pullback at a closure point

If a map of quasi-coherent modules on an algebraic space over an affine base vanishes
on the scheme-theoretic fibres over a subset, it vanishes on the fibre over any point
of the closure.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 77.8.4: In Situation 77.8.1, let `T ⊆ S` be a subset and let `s ∈ S` lie in
the closure of `T`. For `t ∈ T`, write `u_t` for the pullback of `u` to the
scheme-theoretic fibre `X_t`, that is `baseChangeMap (toBase X) (residueFieldHom S t) u`,
equivalently `(pullback (fiberι (toBase X) t)).map u` on `fiber (toBase X) t`, and
likewise `u_s` on `X_s`. If `X` is locally of finite presentation over `S`, `𝒢` is of
finite presentation, and `u_t = 0` for all `t ∈ T`, then `u_s = 0`. -/
@[stacks 0CWB]
theorem baseChangeMap_eq_zero_of_mem_closure
    {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S}
    [LocallyOfFinitePresentation (toBase X)] {ℱ 𝒢 : X.Modules}
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] [𝒢.IsFinitePresentation]
    (hG_flat : flatOver 𝒢 (toBase X)) (u : ℱ ⟶ 𝒢) (T : Set S) {s : S}
    (hs : s ∈ closure T)
    (hT : ∀ t ∈ T, baseChangeMap (toBase X) (residueFieldHom S t) u = 0) :
    baseChangeMap (toBase X) (residueFieldHom S s) u = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
