/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
public import stacks_project.Chap77.Situation_77_13_1_FormalCompletion

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

/-- A compatible system of pseudo-coherent derived modules on the infinitesimal
thickenings of an algebraic space algebraizes to a pseudo-coherent derived module
on the ambient space, compatibly with all transition maps. -/
theorem exists_pseudoCoherent_of_thickenings
    {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
    {X : AlgebraicSpace (Spec A_lim.cone.pt)}
    {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
    {p : ∀ n, Xn n ⟶ X}
    {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
    {i : ∀ n, Xn n ⟶ Xn (n + 1)}
    [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]
    (S : System A A_lim X Xn p q i) :
    ∃ (K : ModuleDerived X)
      (e : ∀ n, (modulePullbackDerived (p n)).obj K ≅ S.K n),
      IsPseudoCoherent X K ∧
        ∀ n,
          (modulePullbackDerived (i n)).map (e (n + 1)).hom ≫
              (S.transitionIso n).hom =
            (modulePullbackDerived.compComparison (i n) (p (n + 1))).app K ≫
              eqToHom (congrArg
                (fun g ↦ (modulePullbackDerived g).obj K) (S.comp_p n)) ≫
              (e n).hom := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System
