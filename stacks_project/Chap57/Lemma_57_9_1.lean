/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor.Resolution
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 57.9.1: for finite-type schemes over a Noetherian ring with the resolution
property, every coherent module on their fiber product admits an epimorphism from an
external tensor product of finite locally free modules. -/
@[stacks 0FZ0] #check
  (AlgebraicGeometry.Scheme.Modules.exists_epi_from_externalTensorProduct :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R))
    [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType g]
    (hX : Scheme.HasResolutionProperty X)
    (hY : Scheme.HasResolutionProperty Y)
    (F : (Limits.pullback f g).Modules) [F.IsCoherent],
    ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
      (G : Y.Modules) (_ : G.IsFiniteLocallyFree)
      (q : Scheme.Modules.externalTensorProduct f g E G ⟶ F), Epi q)
