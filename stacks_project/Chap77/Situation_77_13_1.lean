module

import StacksCheckRecall
import stacks_project.Chap77.Situation_77_13_1_FormalCompletion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion

noncomputable section

universe u

variable (A : SequentialInverseSystem CommRingCat.{u})
variable (A_lim : LimitCone A)
variable (h_surjective : A.Surjective)
variable (h_kernel : A.KernelLocallyNilpotent)

variable (X : AlgebraicSpace (Spec A_lim.cone.pt))
variable [Proper (toBase X)] [Flat (toBase X)] [FinitePresentation (toBase X)]

variable (Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt))
variable (p : ∀ n, Xn n ⟶ X)
variable (q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n)
variable (h_pullback : ∀ n,
  IsPullback (q n) (p n) (Modules.stageSpecToBase A_lim n) (toBase X))
variable [∀ n, IsClosedImmersion (p n)]

variable (i : ∀ n, Xn n ⟶ Xn (n + 1))
variable (hiX : ∀ n, i n ≫ p (n + 1) = p n)
variable (hiA : ∀ n,
  i n ≫ q (n + 1) = q n ≫ Modules.stageSpecTransition A_lim n)

variable (K : ∀ n, ModuleDerived (Xn n))
variable (hK : ∀ n, IsPseudoCoherent (Xn n) (K n))
variable (φ : ∀ n, (modulePullbackDerived (i n)).obj (K (n + 1)) ⟶ K n)
variable [∀ n, IsIso (φ n)]

/- Situation 77.13.1: `A_lim` realizes `A = lim Aₙ`, the transition maps of `A`
are surjective with locally nilpotent kernels, and `toBase X` is proper, flat,
and of finite presentation. Each square defining `Xn n` is cartesian and
`p n : Xn n ⟶ X` is a closed immersion. The pseudo-coherent objects `K n` are
linked by derived-pullback isomorphisms `L(i n)^* K (n + 1) ≅ K n`. -/
@[stacks 0DIK] #check
  (System.of h_surjective h_kernel h_pullback hiX hiA K hK φ :
    System A A_lim X Xn p q i)
