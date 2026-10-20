/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor.Resolution
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace DiagonalResolution

noncomputable section

/-- Every degree of a chain complex is isomorphic to an external tensor product of
finite locally free modules on the source scheme. -/
def IsTermwiseExternalTensorProduct
    {R : Type u} [CommRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (F : ChainComplex ((Limits.pullback f f).Modules) ℕ) : Prop :=
  ∀ n : ℕ, ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
    (G : X.Modules) (_ : G.IsFiniteLocallyFree),
    IsIsomorphic (F.X n) (externalTensorProduct f f E G)

/-- A separated finite-type scheme with the resolution property has a
quasi-isomorphic chain-complex resolution of its diagonal module whose terms are
external tensor products of finite locally free modules. -/
theorem exists_resolution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    [Scheme.Hom.FiniteType f] [IsSeparated f]
    (hX : Scheme.HasResolutionProperty X) :
    ∃ (F : ChainComplex ((Limits.pullback f f).Modules) ℕ)
      (π : F ⟶
        (ChainComplex.single₀ ((Limits.pullback f f).Modules)).obj
          (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))),
      QuasiIso π ∧ IsTermwiseExternalTensorProduct f F := sorry

end

end DiagonalResolution

end AlgebraicGeometry.Scheme.Modules
