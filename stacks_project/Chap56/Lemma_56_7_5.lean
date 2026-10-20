module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.FourierMukai

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 56.7.5: over a field, for finite-type schemes with separated source,
coherent kernels flat over the source with support finite over the target
classify exact linear functors on coherent modules via Fourier--Mukai restriction. -/
@[stacks 0FZN] #check
  (AlgebraicGeometry.Scheme.coherentExactFourierMukai_isEquivalence :
    ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
      [x.FiniteType] [y.FiniteType] [IsSeparated x] [IsNoetherian X]
      [QuasiCompact (Limits.pullback.snd x y)] [QuasiSeparated (Limits.pullback.snd x y)],
      (AlgebraicGeometry.Scheme.coherentExactFourierMukai x y).IsEquivalence)
