module

public import stacks_project.Chap77.Theorem_77_13_6_Derived_Grothendieck_Existence_Theorem_Algebraization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion

noncomputable section

universe u

/- Theorem 77.13.6 (Derived Grothendieck Existence Theorem): in Situation
77.13.1 there exists a pseudo-coherent `K` in `D(𝒪_X)` such that
`L(p n)^* K ≅ K n` for all `n`, compatibly with the maps `φ n`. -/
@[stacks 0DIQ] #check
  (@AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.exists_pseudoCoherent_of_thickenings :
    ∀ {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
      {X : AlgebraicSpace (Spec A_lim.cone.pt)}
      {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
      {p : ∀ n, Xn n ⟶ X}
      {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
      {i : ∀ n, Xn n ⟶ Xn (n + 1)}
      [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]
      (S : System A A_lim X Xn p q i),
      ∃ (K : ModuleDerived X)
        (e : ∀ n, (modulePullbackDerived (p n)).obj K ≅ S.K n),
        IsPseudoCoherent X K ∧
          ∀ n,
            (modulePullbackDerived (i n)).map (e (n + 1)).hom ≫
                (S.transitionIso n).hom =
              (modulePullbackDerived.compComparison (i n) (p (n + 1))).app K ≫
                eqToHom (congrArg
                  (fun g ↦ (modulePullbackDerived g).obj K) (S.comp_p n)) ≫
                (e n).hom)
