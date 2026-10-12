/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ClosedImmersion.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ProjectionFormula.ClosedEmbedding
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.CategoryTheory.Monoidal.Adjunction.SupportedTensor

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X Z : Scheme.{u}} (i : Z ⟶ X)
variable [IsClosedImmersion i] [PseudoCoherent i]
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [KFlat.HomotopyTensorDescends Z.toRingedSpace]
variable [KFlat.TensorDescends Z.toRingedSpace]
variable [KFlat.IsLocalization Z.toRingedSpace]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom i.toShHom)]
variable [Functor.HasLeftDerivedFunctor
  (RingedSpace.modulePullbackToDerived i.toShHom)
  (RingedSpace.ModuleQis X.toRingedSpace)]
variable [HasWeakSheafify (Opens.grothendieckTopology Z.toRingedSpace) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Z.toRingedSpace).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived i.toShHom)]

/-- The canonical comparison morphism
`RHom(𝒪_Z, K) ⊗ᴸ Li^*M ⟶ RHom(𝒪_Z, K ⊗ᴸ M)`, obtained from the
closed-immersion projection formula and the counit of derived pushforward/internal Hom. -/
noncomputable def internalHomTensorPullbackComparison
    (K : Plus X) (M : Scheme.ModuleDerived.Quasicoherent X) :
    (ClosedImmersion.rHomFromStructureSheaf i.toShHom
        (IsClosedImmersion.isClosedEmbedding i)).obj K.obj.obj ⊗
        (RingedSpace.modulePullbackDerived i.toShHom).obj M.obj ⟶
      (ClosedImmersion.rHomFromStructureSheaf i.toShHom
        (IsClosedImmersion.isClosedEmbedding i)).obj (K.obj.obj ⊗ M.obj) :=
  (β_ _ _).hom ≫
    (@Adjunction.supportTensor _ _ _ _ _ _ _ _ _
      (RingedSpace.modulePullbackDerivedPushforwardAdjunction i.toShHom)
      (ClosedImmersion.adjunction i.toShHom
        (IsClosedImmersion.isClosedEmbedding i)) _
      (ClosedEmbedding.projectionFormula i.toShHom
        (IsClosedImmersion.isClosedEmbedding i)) M.obj K.obj.obj) ≫
    (ClosedImmersion.rHomFromStructureSheaf i.toShHom
      (IsClosedImmersion.isClosedEmbedding i)).map (β_ M.obj K.obj.obj).hom

/-- For a pseudo-coherent closed immersion `i : Z ⟶ X`, a bounded-below
quasicoherent derived module `K`, and a quasicoherent derived module `M` locally
of Tor-amplitude in `[a, ∞)`, the canonical comparison
`RHom(𝒪_Z, K) ⊗ᴸ Li^*M ⟶ RHom(𝒪_Z, K ⊗ᴸ M)` is an isomorphism. -/
theorem internalHomTensorPullbackComparison_isIso
    (K : Plus X) (M : Scheme.ModuleDerived.Quasicoherent X) (a : ℤ)
    (hM : ∃ (J : Type u) (U : J → X.Opens),
      TopologicalSpace.IsOpenCover U ∧ ∀ j : J,
        RingedSpace.HasTorAmplitudeGE
          ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace (U j)).obj M.obj) a) :
    IsIso (internalHomTensorPullbackComparison i K M) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
