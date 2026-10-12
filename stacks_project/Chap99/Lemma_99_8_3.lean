/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_8_3_SpacePoint
public import stacks_project.Chap99.Lemma_99_8_3_Sheaf

/-!
# Lemma 99.8.3

In Situation 99.8.1, morphisms of fppf sheaves from an algebraic space `T` over
`S` into `Quot_{F/X/B}` are identified with pairs `(h, F_T ⟶ Q)` where
`h : T ⟶ B` and `Q` is a finitely presented `T`-flat quotient of the pullback
of `F` to `X ×_{B,h} T` whose support is proper over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.8.3: in Situation 99.8.1, let `T` be an algebraic space over `S`.
Morphisms of fppf sheaves `T ⟶ Quot_{F/X/B}` on `(Sch/S)_fppf` are in bijection
with pairs `(h, F_T ⟶ Q)` where `h : T ⟶ B` and `Q` is a finitely presented
`T`-flat quotient of the pullback of `F` to `X ×_{B,h} T` whose support is
proper over `T`, identified by kernels. -/
@[stacks 0D3V]
theorem quotSheafHom_bijective (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] (T : AlgebraicSpace S) :
    Function.Bijective (toQuotSheafHom f F T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
