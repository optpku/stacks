/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The underlying reverse kernel `swap^* RHom(K, a(𝒪_Y))` on `Y ×_S X`. -/
noncomputable def reverseKernelUnderlying
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g)) :
    RingedSpace.ModuleDerived (Limits.pullback g f).toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    (Limits.pullbackSymmetry g f).hom.toShHom).obj
      ((MonoidalClosed.ihomOf H K.obj).obj
        (a.obj (Scheme.DerivedQCoh.structureSheaf Y)).obj)

/-- A pseudo-coherent kernel makes the underlying reverse kernel quasicoherent. -/
theorem reverseKernelUnderlying_quasicoherent
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a) :
    Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback g f)
      (reverseKernelUnderlying f g H K a) := sorry

/-- The reverse Fourier--Mukai kernel on `Y ×_S X`, with its quasicoherence law separated
from the explicit internal-Hom and factor-swap construction. -/
noncomputable def reverseKernel
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a) :
    Scheme.DerivedQCoh (Limits.pullback g f) :=
  ⟨reverseKernelUnderlying f g H K a,
    reverseKernelUnderlying_quasicoherent f g H K hK a aAdjunction⟩

/-- Forgetting quasicoherence identifies `reverseKernel` with
`swap^* RHom(K, a(𝒪_Y))`. -/
theorem reverseKernel_obj
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a) :
    (reverseKernel f g H K hK a aAdjunction).obj =
      reverseKernelUnderlying f g H K a := sorry

/-- The Fourier--Mukai transform associated to the reverse kernel. -/
noncomputable def reverseTransform
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a) :
    Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X :=
  quasicoherent g f (reverseKernel f g H K hK a aAdjunction)

/-- The reverse transform is the Fourier--Mukai transform associated to `reverseKernel`. -/
theorem reverseTransform_eq
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a) :
    reverseTransform f g H K hK a aAdjunction =
      quasicoherent g f (reverseKernel f g H K hK a aAdjunction) := sorry

/-- The family of maps from morphisms into the reverse Fourier–Mukai transform to morphisms
from the forward Fourier–Mukai transform. -/
abbrev homComparisonFamily {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a) : Type (u + 1) :=
  ∀ (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y),
    (M ⟶ (reverseTransform f g H K hK a aAdjunction).obj N) →
      ((quasicoherent f g K).obj M ⟶ N)

/-- The identity functor on a homotopy category is naturally isomorphic to the functor induced by
the identity functor before passage to homotopy categories. -/
private theorem homotopyIdentityIso_naturality
    (A : Type u) [Category A] [Preadditive A]
    {K L : HomotopyCategory A (ComplexShape.up ℤ)} (k : K ⟶ L) :
    ((Functor.id A).mapHomotopyCategory (ComplexShape.up ℤ)).map k ≫ 𝟙 L =
      𝟙 K ≫ k := sorry

/-- The componentwise identity comparison between the homotopy functor induced by the identity
and the identity functor on the homotopy category. -/
private noncomputable def homotopyIdentityIso
    (A : Type u) [Category A] [Preadditive A] :
    (Functor.id A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      Functor.id (HomotopyCategory A (ComplexShape.up ℤ)) :=
  NatIso.ofComponents (fun K ↦ Iso.refl K)
    (fun k ↦ homotopyIdentityIso_naturality A k)

/-- The underived pullback along the identity, followed by localization, agrees with the
homotopy-to-derived localization functor. -/
private noncomputable def modulePullbackToDerivedIdIso (Z : RingedSpace.{u}) :
    RingedSpace.modulePullbackToDerived (𝟙 Z) ≅
      (DerivedCategory.Qh : HomotopyCategory Z.Modules (ComplexShape.up ℤ) ⥤
        RingedSpace.ModuleDerived Z) :=
  ((Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryIso (RingedSpace.Hom.pullbackIdIso Z))
        (DerivedCategory.Qh : HomotopyCategory Z.Modules (ComplexShape.up ℤ) ⥤
          RingedSpace.ModuleDerived Z)).trans
      (Functor.isoWhiskerRight (homotopyIdentityIso Z.Modules)
        (DerivedCategory.Qh : HomotopyCategory Z.Modules (ComplexShape.up ℤ) ⥤
          RingedSpace.ModuleDerived Z))).trans (Functor.leftUnitor _)

/-- Derived pullback along the identity is canonically isomorphic to the identity functor. -/
private noncomputable def modulePullbackDerivedIdIso (Z : RingedSpace.{u}) :
    RingedSpace.modulePullbackDerived (𝟙 Z) ≅
      Functor.id (RingedSpace.ModuleDerived Z) :=
  let Q := (DerivedCategory.Qh :
    HomotopyCategory Z.Modules (ComplexShape.up ℤ) ⥤ RingedSpace.ModuleDerived Z)
  let W := HomotopyCategory.quasiIso Z.Modules (ComplexShape.up ℤ)
  let e : Q ⋙ Functor.id (RingedSpace.ModuleDerived Z) ≅
      RingedSpace.modulePullbackToDerived (𝟙 Z) :=
    (Functor.rightUnitor Q).trans (modulePullbackToDerivedIdIso Z).symm
  -- Local instance justification (proof-local temporary data): e identifies the identity model with the specified pullback source; leftDerivedNatIso uses this exact counit witness.
  let _ : (Functor.id (RingedSpace.ModuleDerived Z)).IsLeftDerivedFunctor e.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ e
  let alpha : Q ⋙ RingedSpace.modulePullbackDerived (𝟙 Z) ⟶
      RingedSpace.modulePullbackToDerived (𝟙 Z) :=
    (RingedSpace.modulePullbackToDerived (𝟙 Z)).totalLeftDerivedCounit Q W
  Functor.leftDerivedNatIso
    (RingedSpace.modulePullbackDerived (𝟙 Z))
    (Functor.id (RingedSpace.ModuleDerived Z)) alpha e.hom W (Iso.refl _)

/-- Pulling the second projection of `Y ×_S X` back through factor swap gives the first
projection of `X ×_S Y`. -/
noncomputable def swapPullbackSndIso
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (M : Scheme.DerivedQCoh X) :
    (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom).obj
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.snd g f)).obj M).obj ≅
      ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst f g)).obj M).obj :=
  ((Scheme.DerivedQCoh.pullback.inclusionIso
      (Limits.pullbackSymmetry g f).inv).app
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.snd g f)).obj M)).symm.trans
    ((Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g)).ι.mapIso
      ((Scheme.DerivedQCoh.pullbackCompAppIso
          (Limits.pullbackSymmetry g f).inv (Limits.pullback.snd g f)
          (RingedSpace.modulePullbackDerived.compComparison_isIso _ _) M).trans
        (eqToIso (congrArg
          (fun q : Limits.pullback f g ⟶ X ↦
            (Scheme.DerivedQCoh.pullback q).obj M)
          (Limits.pullbackSymmetry_inv_comp_snd g f)))))

/-- Pulling the first projection of `Y ×_S X` back through factor swap gives the second
projection of `X ×_S Y`. -/
noncomputable def swapPullbackFstIso
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (N : Scheme.DerivedQCoh Y) :
    (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom).obj
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst g f)).obj N).obj ≅
      ((Scheme.DerivedQCoh.pullback (Limits.pullback.snd f g)).obj N).obj :=
  ((Scheme.DerivedQCoh.pullback.inclusionIso
      (Limits.pullbackSymmetry g f).inv).app
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst g f)).obj N)).symm.trans
    ((Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g)).ι.mapIso
      ((Scheme.DerivedQCoh.pullbackCompAppIso
          (Limits.pullbackSymmetry g f).inv (Limits.pullback.fst g f)
          (RingedSpace.modulePullbackDerived.compComparison_isIso _ _) N).trans
        (eqToIso (congrArg
          (fun q : Limits.pullback f g ⟶ Y ↦
            (Scheme.DerivedQCoh.pullback q).obj N)
          (Limits.pullbackSymmetry_inv_comp_fst g f)))))

/-- Pulling the reverse kernel back through the inverse factor swap recovers
`RHom(K, a(𝒪_Y))`. -/
@[no_expose] noncomputable def reverseKernelCancelIso
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a) :
    (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom).obj
        (reverseKernel f g H K hK a aAdjunction).obj ≅
      (MonoidalClosed.ihomOf H K.obj).obj
        (a.obj (Scheme.DerivedQCoh.structureSheaf Y)).obj :=
  let I := (MonoidalClosed.ihomOf H K.obj).obj
    (a.obj (Scheme.DerivedQCoh.structureSheaf Y)).obj
  ((RingedSpace.modulePullbackDerived.compIso
      (Limits.pullbackSymmetry g f).inv.toShHom
      (Limits.pullbackSymmetry g f).hom.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso _ _)).app I).trans
    ((eqToIso (congrArg
      (fun q : Limits.pullback f g ⟶ Limits.pullback f g ↦
        (RingedSpace.modulePullbackDerived q.toShHom).obj I)
      (Limits.pullbackSymmetry g f).inv_hom_id)).trans
        ((modulePullbackDerivedIdIso (Limits.pullback f g).toRingedSpace).app I))

/-- A morphism into the reverse transform, transposed across the reverse pushforward and factor
swap, as a morphism into `pr₂^*N ⊗ RHom(K, a(𝒪_Y))`. -/
noncomputable def reverseAdjointTransport
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y)
    (phi : M ⟶ (reverseTransform f g H K hK a aAdjunction).obj N) :
    ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst f g)).obj M).obj ⟶
      ((Scheme.DerivedQCoh.pullback (Limits.pullback.snd f g)).obj N).obj ⊗
        (MonoidalClosed.ihomOf H K.obj).obj
          (a.obj (Scheme.DerivedQCoh.structureSheaf Y)).obj :=
  let t := (Limits.pullbackSymmetry g f).inv
  let A := (Scheme.DerivedQCoh.pullback (Limits.pullback.fst g f)).obj N
  let K' := reverseKernel f g H K hK a aAdjunction
  let transformObjIso :
      (reverseTransform f g H K hK a aAdjunction).obj N ≅
        (Scheme.DerivedQCoh.pushforwardCohomologyIn
          (Limits.pullback.snd g f)).obj (Scheme.DerivedQCoh.tensorObj A K') :=
    Iso.refl _
  let phiAdj := ((Scheme.DerivedQCoh.pullbackPushforwardAdjunction
    (Limits.pullback.snd g f)).homEquiv M _).symm (phi ≫ transformObjIso.hom)
  (swapPullbackSndIso f g M).inv ≫
    (RingedSpace.modulePullbackDerived t.toShHom).map phiAdj.hom ≫
    (RingedSpace.modulePullbackDerived t.toShHom).map
      (Scheme.DerivedQCoh.tensorObjIsoTensor A K').hom ≫
    (Functor.Monoidal.μIso
      (RingedSpace.modulePullbackDerived t.toShHom) A.obj K'.obj).inv ≫
    ((swapPullbackFstIso f g N).hom ⊗ₘ
      (reverseKernelCancelIso f g H K hK a aAdjunction).hom)

/-- The internal-Hom mate associated to a morphism into the reverse Fourier--Mukai transform. -/
noncomputable def comparisonKernelMap
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y)
    (phi : M ⟶ (reverseTransform f g H K hK a aAdjunction).obj N) :
    Scheme.DerivedQCoh.tensorObj
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst f g)).obj M) K ⟶
      Scheme.DerivedQCoh.tensorObj
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.snd f g)).obj N)
          (a.obj (Scheme.DerivedQCoh.structureSheaf Y)) :=
  let A := (Scheme.DerivedQCoh.pullback (Limits.pullback.fst f g)).obj M
  let B := (Scheme.DerivedQCoh.pullback (Limits.pullback.snd f g)).obj N
  let I := (MonoidalClosed.ihomOf H K.obj).obj
    (a.obj (Scheme.DerivedQCoh.structureSheaf Y)).obj
  let aO := a.obj (Scheme.DerivedQCoh.structureSheaf Y)
  ⟨(Scheme.DerivedQCoh.tensorObjIsoTensor A K).hom ≫
    (reverseAdjointTransport f g H K hK a aAdjunction M N phi ⊗ₘ 𝟙 K.obj) ≫
    (α_ B.obj I K.obj).hom ≫
    (B.obj ◁ ((β_ I K.obj).hom ≫
      (MonoidalClosed.adjunctionOf H K.obj).counit.app aO.obj)) ≫
    (Scheme.DerivedQCoh.tensorObjIsoTensor B aO).inv⟩

/-- The internal-Hom mate is the explicit factor-swap transport followed by braiding and the
counit of `K ⊗ - ⊣ RHom(K, -)`. -/
theorem comparisonKernelMap_spec
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y)
    (phi : M ⟶ (reverseTransform f g H K hK a aAdjunction).obj N) :
    comparisonKernelMap f g H K hK a aAdjunction M N phi =
      let A := (Scheme.DerivedQCoh.pullback (Limits.pullback.fst f g)).obj M
      let B := (Scheme.DerivedQCoh.pullback (Limits.pullback.snd f g)).obj N
      let I := (MonoidalClosed.ihomOf H K.obj).obj
        (a.obj (Scheme.DerivedQCoh.structureSheaf Y)).obj
      let aO := a.obj (Scheme.DerivedQCoh.structureSheaf Y)
      ⟨(Scheme.DerivedQCoh.tensorObjIsoTensor A K).hom ≫
        (reverseAdjointTransport f g H K hK a aAdjunction M N phi ⊗ₘ 𝟙 K.obj) ≫
        (α_ B.obj I K.obj).hom ≫
        (B.obj ◁ ((β_ I K.obj).hom ≫
          (MonoidalClosed.adjunctionOf H K.obj).counit.app aO.obj)) ≫
        (Scheme.DerivedQCoh.tensorObjIsoTensor B aO).inv⟩ := sorry

/-- The canonical Hom comparison obtained by the internal-Hom mate, the projection-formula
duality comparison, and the chosen adjunction `Rpr₂_* ⊣ a`. -/
noncomputable def homComparison
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.snd f g).toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a) :
    homComparisonFamily f g H K hK a aAdjunction :=
  fun M N phi ↦
    (aAdjunction.homEquiv _ _).symm
      (comparisonKernelMap f g H K hK a aAdjunction M N phi ≫
        Scheme.DerivedQCoh.pullbackTensorDualityMap
          (Limits.pullback.snd f g) a aAdjunction N)

/-- The Hom comparison is the adjoint transpose of the explicit internal-Hom mate followed by
the projection-formula duality map. -/
theorem homComparison_spec
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.snd f g).toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y)
    (phi : M ⟶ (reverseTransform f g H K hK a aAdjunction).obj N) :
    homComparison f g H K hK a aAdjunction M N phi =
      (aAdjunction.homEquiv _ _).symm
        (comparisonKernelMap f g H K hK a aAdjunction M N phi ≫
          Scheme.DerivedQCoh.pullbackTensorDualityMap
            (Limits.pullback.snd f g) a aAdjunction N) := sorry

/-- The Hom comparison is natural in the source object. -/
theorem homComparison_natural_left
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.snd f g).toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    {M₁ M₂ : Scheme.DerivedQCoh X} (u : M₁ ⟶ M₂)
    (N : Scheme.DerivedQCoh Y)
    (phi : M₂ ⟶ (reverseTransform f g H K hK a aAdjunction).obj N) :
    homComparison f g H K hK a aAdjunction M₁ N (u ≫ phi) =
      (quasicoherent f g K).map u ≫
        homComparison f g H K hK a aAdjunction M₂ N phi := sorry

/-- The Hom comparison is natural in the target object. -/
theorem homComparison_natural_right
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.snd f g).toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    (M : Scheme.DerivedQCoh X) {N₁ N₂ : Scheme.DerivedQCoh Y}
    (v : N₁ ⟶ N₂)
    (phi : M ⟶ (reverseTransform f g H K hK a aAdjunction).obj N₁) :
    homComparison f g H K hK a aAdjunction M N₂
        (phi ≫ (reverseTransform f g H K hK a aAdjunction).map v) =
      homComparison f g H K hK a aAdjunction M N₁ phi ≫ v := sorry

/-- The Hom comparison is bijective when the target object is perfect. -/
theorem homComparison_bijective_of_perfect_target
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.snd f g).toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y)
    (hN : RingedSpace.ModuleDerived.IsPerfect N.obj) :
    Function.Bijective (homComparison f g H K hK a aAdjunction M N) := sorry

/-- The Hom comparison is bijective for every target when the kernel is perfect and the first
structural morphism is proper, flat, and finitely presented. -/
theorem homComparison_bijective_of_perfect_kernel
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.snd f g).toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (hK_perfect : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y) :
    Function.Bijective (homComparison f g H K hK a aAdjunction M N) := sorry

end AlgebraicGeometry.Scheme.FourierMukai
