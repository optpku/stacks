/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_21_2_Functor
import StacksCheckRecall

/-!
# Infinitesimal and tangent functors of a deformation object

Under condition (RS*), a category fibred in groupoids over `(Sch/S)_fppf` has
A-linear functors Inf_x and T_x on Mod_A, comparing infinitesimal automorphisms
and isomorphism classes of lifts along first-order thickenings.
-/

@[expose] public section

open AlgebraicGeometry.GroupoidsOver

/- Lemma 98.21.2 (1). Let S be a scheme, let X be a category fibred in groupoids
over (Sch/S)_fppf satisfying (RS*), let A be an S-algebra and let x be an object
of X over Spec(A). There is an A-linear functor Inf_x : Mod_A ⥤ Mod_A such that
for a square-zero thickening A' ⟶ A with kernel I and a lift x' of x there is an
isomorphism Inf_x(I) ≅ Inf(x'/x). Lean records Inf_x as infFunctor, with comparison
iso infIso. -/
@[stacks 07Y9] #check infFunctor

/- Lemma 98.21.2 (2). In the same setting there is an A-linear functor
T_x : Mod_A ⥤ Mod_A such that for M in Mod_A there is a bijection
T_x(M) → Lift(x, A[M]), and for a square-zero thickening A' ⟶ A with kernel I
there is an action T_x(I) × Lift(x, A') ⟶ Lift(x, A') which is simply transitive
when Lift(x, A') is nonempty. Lean records T_x as tangentFunctor, with underlying
bijection tangentForget and action tangentAction. -/
@[stacks 07Y9] #check tangentFunctor

/- The comparison isomorphism Inf_x(I) ≅ Inf(x'/x) of A-modules. -/
#check infIso

/- The forgetful identification of the underlying type of T_x(M) with Lift(x, A[M]). -/
#check tangentForget

/- The action of T_x(I) on Lift(x, A'). -/
#check tangentAction

/- Inf_x is A-linear. -/
#check infFunctor.instModuleLinear

/- T_x is A-linear. -/
#check tangentFunctor.instModuleLinear

/- The action of T_x(I) is simply transitive on a nonempty set of lifts. -/
#check tangentAction_simplyTransitive
