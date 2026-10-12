/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RepresentationTheory.PGroup
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 59.66.3: a finite module over a Noetherian group algebra, annihilated by
`ell ^ n`, admits a finite filtration whose successive quotients have trivial
`H`-action. -/
@[stacks 0GIZ] #check (Module.existsFiniteTrivialActionFiltration :
    ∀ {Λ : Type u} {H : Type v} {M : Type w}
    [CommRing Λ] [IsNoetherianRing Λ]
    [Group H] [Finite H]
    [AddCommGroup M] [Module (MonoidAlgebra Λ H) M]
    [Module.Finite (MonoidAlgebra Λ H) M]
    (ell n : ℕ) [Fact (Nat.Prime ell)]
    (hn : 1 ≤ n) (hH : IsPGroup ell H)
    (h_ann : ∀ m : M, (ell ^ n) • m = 0),
    ∃ s : RelSeries
        ({p : Submodule (MonoidAlgebra Λ H) M × Submodule (MonoidAlgebra Λ H) M |
          p.1 ≤ p.2 ∧
            ∀ h : H, ∀ x : p.2 ⧸ p.1.submoduleOf p.2,
              (MonoidAlgebra.single h (1 : Λ)) • x = x} : SetRel _ _),
      s.head = ⊥ ∧ s.last = ⊤)
