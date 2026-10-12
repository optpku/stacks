/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_7_5_SpacePoint
public import stacks_project.Chap99.Lemma_99_7_5_Sheaf

/-!
# Lemma 99.7.5

In Situation 99.7.1, morphisms of fppf sheaves from an algebraic space `T` over
`S` into `Q_{F/X/B}` (resp. `Q^{fp}_{F/X/B}`) are identified with pairs
`(h, F_T ⟶ Q)` where `h : T ⟶ B` and `Q` is quasi-coherent and flat over `T`
(resp. of finite presentation and flat over `T`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.7.5 (1): in Situation 99.7.1, let `T` be an algebraic space over `S`.
Morphisms of fppf sheaves `T ⟶ Q_{F/X/B}` on `(Sch/S)_fppf` are in bijection with
pairs `(h, F_T ⟶ Q)` where `h : T ⟶ B` and `Q` is a quasi-coherent quotient of the
pullback of `F` to `X ×_{B,h} T` that is flat over `T`, identified by kernels. -/
@[stacks 0D3U]
theorem sheafHom_bijective (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (T : AlgebraicSpace S) :
    Function.Bijective (toSheafHom f F T) := sorry

/-- Lemma 99.7.5 (2): in Situation 99.7.1, let `T` be an algebraic space over `S`.
Morphisms of fppf sheaves `T ⟶ Q^{fp}_{F/X/B}` on `(Sch/S)_fppf` are in bijection
with pairs `(h, F_T ⟶ Q)` where `h : T ⟶ B` and `Q` is a finitely presented
quasi-coherent quotient of the pullback of `F` to `X ×_{B,h} T` that is flat over
`T`, identified by kernels. -/
@[stacks 0D3U]
theorem fpSheafHom_bijective (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (T : AlgebraicSpace S) :
    Function.Bijective (toFpSheafHom f F T) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
