/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.«63_11_4_1_Trace»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.Etale

/- 63.11.4.1: for a separated finite-type morphism `f : X ⟶ Y` of
quasi-compact quasi-separated schemes and a torsion coefficient ring `Λ`,
and for `L` in `D(X_étale, Λ)` and `K` in `D(Y_étale, Λ)`, there is a
canonical sheafy-trace morphism
`Rf_* RHom_Λ(L, Rf^! K) ⟶ RHom_Λ(Rf_! L, K)`, the Remark 63.10.9
internal-Hom comparison `α` at `(L, Rf^! K)` followed by
`RHom(Rf_! L, ε_K)` for the counit `ε` of `Rf_! ⊣ Rf^!`. -/
@[stacks 0GLB] #check etaleDerivedSheafyTrace

end
