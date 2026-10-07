module

public import stacks_project.Chap57.Lemma_57_8_8_Transform
public import stacks_project.Chap57.Lemma_57_8_7_Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.TraceComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- A morphism `N ⟶ Φ(M)` transposed across the forward pushforward as
`pr₂^* N ⟶ pr₁^* M ⊗ K`. -/
noncomputable def dualForwardAdjointTransport
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    [CompactSpace (Limits.pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback f g : Scheme.{u})]
    [CompactSpace (Limits.pullback g f : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})]
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y)
    (phi : N ⟶ (quasicoherent f g K).obj M) :
    ((Scheme.DerivedQCoh.pullback (Limits.pullback.snd f g)).obj N).obj ⟶
      ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst f g)).obj M).obj ⊗ K.obj :=
  let A := (Scheme.DerivedQCoh.pullback (Limits.pullback.fst f g)).obj M
  let transformObjIso :
      (quasicoherent f g K).obj M ≅
        (Scheme.DerivedQCoh.pushforwardCohomologyIn
          (Limits.pullback.snd f g)).obj (Scheme.DerivedQCoh.tensorObj A K) :=
    Iso.refl _
  let phiAdj := ((Scheme.DerivedQCoh.pullbackPushforwardAdjunction
    (Limits.pullback.snd f g)).homEquiv N _).symm (phi ≫ transformObjIso.hom)
  phiAdj.hom ≫ (Scheme.DerivedQCoh.tensorObjIsoTensor A K).hom

/-- The internal-Hom mate associated to a morphism into the forward Fourier--Mukai transform,
as a morphism `pr₁^* N ⊗ K' ⟶ pr₂^* M ⊗ a(𝒪_X)` on `Y ×_S X`. -/
noncomputable def dualComparisonKernelMap
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HomotopyTensorDescends (Limits.pullback g f).toRingedSpace]
    [TensorDescends (Limits.pullback g f).toRingedSpace]
    [IsLocalization (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).hom.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    [CompactSpace (Limits.pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback f g : Scheme.{u})]
    [CompactSpace (Limits.pullback g f : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})]
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y)
    (phi : N ⟶ (quasicoherent f g K).obj M) :
    Scheme.DerivedQCoh.tensorObj
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst g f)).obj N)
        (dualKernel f g H K hK a aAdjunction) ⟶
      (Scheme.DerivedQCoh.finiteRightAdjoint
        (Limits.pullback.snd g f)).obj M :=
  let A := (Scheme.DerivedQCoh.pullback (Limits.pullback.fst f g)).obj M
  let B := (Scheme.DerivedQCoh.pullback (Limits.pullback.snd f g)).obj N
  let I := (MonoidalClosed.ihomOf H K.obj).obj
    (Scheme.DerivedQCoh.structureSheaf (Limits.pullback f g)).obj
  let mate : B.obj ⊗ I ⟶ A.obj :=
    (dualForwardAdjointTransport f g H K hK a aAdjunction M N phi ▷ I) ≫
      (α_ A.obj K.obj I).hom ≫
      (A.obj ◁ (MonoidalClosed.adjunctionOf H K.obj).counit.app
        (Scheme.DerivedQCoh.structureSheaf (Limits.pullback f g)).obj) ≫
      (A.obj ◁ (Scheme.DerivedQCoh.structureSheafUnitIso
        (Limits.pullback f g)).hom) ≫
      (ρ_ A.obj).hom
  have _ := mate
  0

/-- The Hom family for the canonical comparison from the forward Fourier--Mukai transform to the
dual-kernel transform. -/
abbrev dualHomComparisonFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HomotopyTensorDescends (Limits.pullback g f).toRingedSpace]
    [TensorDescends (Limits.pullback g f).toRingedSpace]
    [IsLocalization (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).hom.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    [CompactSpace (Limits.pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback f g : Scheme.{u})]
    [CompactSpace (Limits.pullback g f : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})]
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) : Type (u + 1) :=
  ∀ (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y),
    (N ⟶ (quasicoherent f g K).obj M) →
      ((dualTransform f g H K hK a aAdjunction).obj N ⟶ M)

/-- The canonical comparison `Hom_Y(N, Φ(M)) → Hom_X(Φ'(N), M)` obtained by the internal-Hom
mate, the projection-formula duality map, and the adjunction `Rpr₂_* ⊣ a_X`. -/
noncomputable def dualHomComparison
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HomotopyTensorDescends (Limits.pullback g f).toRingedSpace]
    [TensorDescends (Limits.pullback g f).toRingedSpace]
    [IsLocalization (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).hom.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    [CompactSpace (Limits.pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback f g : Scheme.{u})]
    [CompactSpace (Limits.pullback g f : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})]
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    dualHomComparisonFamily f g H K hK a aAdjunction :=
  fun M N phi ↦
    ((Scheme.DerivedQCoh.finitePushforwardAdjunction
        (Limits.pullback.snd g f)).homEquiv
        (Scheme.DerivedQCoh.tensorObj
          ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst g f)).obj N)
          (dualKernel f g H K hK a aAdjunction)) M).symm
      (dualComparisonKernelMap f g H K hK a aAdjunction M N phi)

/-- The dual Hom comparison is the adjoint transpose of the dual-kernel tensor morphism
followed by the projection-formula duality map. -/
theorem dualHomComparison_spec
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HomotopyTensorDescends (Limits.pullback g f).toRingedSpace]
    [TensorDescends (Limits.pullback g f).toRingedSpace]
    [IsLocalization (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).hom.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    [CompactSpace (Limits.pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback f g : Scheme.{u})]
    [CompactSpace (Limits.pullback g f : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})]
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y)
    (phi : N ⟶ (quasicoherent f g K).obj M) :
    dualHomComparison f g H K hK a aAdjunction M N phi =
      ((Scheme.DerivedQCoh.finitePushforwardAdjunction
          (Limits.pullback.snd g f)).homEquiv
          (Scheme.DerivedQCoh.tensorObj
            ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst g f)).obj N)
            (dualKernel f g H K hK a aAdjunction)) M).symm
        (dualComparisonKernelMap f g H K hK a aAdjunction M N phi) := sorry

end AlgebraicGeometry.Scheme.FourierMukai
