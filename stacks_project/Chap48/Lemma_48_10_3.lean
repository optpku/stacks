/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ClosedImmersion.InternalHom.Tensor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

/- Lemma 48.10.3: Let `i : Z ⟶ X` be a pseudo-coherent closed immersion.
Let `M ∈ D_QCoh(𝒪_X)` locally have Tor-amplitude in `[a, ∞)`, and let
`K ∈ D_QCoh⁺(𝒪_X)`. Then the canonical comparison
`RHom(𝒪_Z, K) ⊗ᴸ Li^*M ⟶ RHom(𝒪_Z, K ⊗ᴸ M)` is an isomorphism. -/
@[stacks 0E2N] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.internalHomTensorPullbackComparison_isIso :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [PseudoCoherent i]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace] [KFlat.IsLocalization X.toRingedSpace]
      [KFlat.HomotopyTensorDescends Z.toRingedSpace]
      [KFlat.TensorDescends Z.toRingedSpace] [KFlat.IsLocalization Z.toRingedSpace]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom i.toShHom)]
      [Functor.HasLeftDerivedFunctor
        (RingedSpace.modulePullbackToDerived i.toShHom)
        (RingedSpace.ModuleQis X.toRingedSpace)]
      [HasWeakSheafify (Opens.grothendieckTopology Z.toRingedSpace) AddCommGrpCat.{u}]
      [(Opens.grothendieckTopology Z.toRingedSpace).WEqualsLocallyBijective AddCommGrpCat.{u}]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived i.toShHom)]
      (K : Scheme.DerivedQCoh.Plus X) (M : Scheme.ModuleDerived.Quasicoherent X) (a : ℤ),
      (∃ (J : Type u) (U : J → X.Opens), TopologicalSpace.IsOpenCover U ∧ ∀ j : J,
        RingedSpace.HasTorAmplitudeGE
          ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace (U j)).obj M.obj) a) →
        IsIso (Scheme.DerivedQCoh.internalHomTensorPullbackComparison i K M))
