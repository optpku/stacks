module

public import ReasLib.LinearAlgebra.Trace.GroupAlgebra
import StacksCheckRecall

@[expose] public section

open scoped MonoidAlgebra Ring

universe u v w

/- Lemma 64.15.3. The coefficient-ring trace of an endomorphism of a finite
projective `Λ[G]`-module is `Nat.card G` times its G-trace in `Λ♮`. -/
@[stacks 03U7] #check (LinearMap.FiniteProjective.traceNatural_eq_card_smul_traceG :
  ∀ {Λ : Type u} {G : Type v} {P : Type w}
    [Ring Λ] [Group G] [Finite G]
    [AddCommGroup P] [Module (Λ[G]) P] [Module Λ P] [IsScalarTower Λ (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]
    (f : Module.End (Λ[G]) P),
    LinearMap.FiniteProjective.traceNatural_restrictScalars f =
      Nat.card G • LinearMap.FiniteProjective.traceG f)
