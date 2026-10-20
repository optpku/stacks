module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Devissage
import StacksCheckRecall

/-!
# Lemma 69.14.2

On a Noetherian algebraic space, a coherent module whose scheme-theoretic support
is reduced with irreducible underlying space admits a dévissage step: a monomorphism
from the pushforward of a finite coproduct of a nonzero coherent ideal sheaf, with
cokernel supported on a proper closed subset of the support.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Lemma 69.14.2: let `S` be a scheme, let `X` be a Noetherian algebraic space over
`S`, and let `F` be a coherent `𝒪_X`-module. If `i : Z ⟶ X` is a scheme-theoretic
support of `F` with `Z` reduced and `|Z|` irreducible, then there exist an integer
`r > 0`, a nonzero ideal sheaf `I ⊂ 𝒪_Z`, and a monomorphism
`(pushforward i).obj (∐ fun _ : Fin r ↦ I.toModule) ⟶ F` of coherent sheaves whose
cokernel is supported on a proper closed subspace of `Z`. -/
@[stacks 07UQ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.exists_coherentIdeal_coproduct_pushforward_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    {Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsSchemeTheoreticSupport F i] [IsReduced Z] [IsIrreducible Z],
    ∃ (r : ℕ) (I : IdealSubobject Z)
      (φ : (pushforward i).obj (∐ fun _ : Fin r ↦ I.toModule) ⟶ F)
      (W : TopologicalSpace.Closeds (Points X)),
      0 < r ∧ I ≠ ⊥ ∧ I.toModule.IsCoherent ∧
        ((pushforward i).obj (∐ fun _ : Fin r ↦ I.toModule)).IsCoherent ∧
        Mono φ ∧ moduleSupport (cokernel φ) ⊆ (W : Set (Points X)) ∧
          (W : Set (Points X)) ⊂ Set.range (Points.map i))
