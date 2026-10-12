/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor.DiagonalResolution
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 57.9.3: for a Noetherian commutative ring `R` and a separated finite-type
morphism `f : X ⟶ Spec (CommRingCat.of R)` with the resolution property, the diagonal
module has a quasi-isomorphic chain-complex resolution whose terms are external tensor
products of finite locally free `X.Modules`. -/
@[stacks 0FZ2] #check
  (AlgebraicGeometry.Scheme.Modules.DiagonalResolution.exists_resolution :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    [Scheme.Hom.FiniteType f] [IsSeparated f]
    (hX : Scheme.HasResolutionProperty X),
    ∃ (F : ChainComplex ((Limits.pullback f f).Modules) ℕ)
      (π : F ⟶
        (ChainComplex.single₀ ((Limits.pullback f f).Modules)).obj
          (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))),
      QuasiIso π ∧
        AlgebraicGeometry.Scheme.Modules.DiagonalResolution.IsTermwiseExternalTensorProduct f F)
