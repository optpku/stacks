/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The objectwise canonical comparison from iterated `DerivedQCoh` pullback to pullback
along a composite scheme morphism. -/
noncomputable def pullbackCompAppIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
      f.toShHom g.toShHom)) (K : DerivedQCoh Z) :
    (pullback f).obj ((pullback g).obj K) ≅ (pullback (f ≫ g)).obj K :=
  (ModuleDerived.quasicoherentProperty X).fullyFaithfulι.preimageIso
    ((pullback.inclusionIso f).app ((pullback g).obj K) ≪≫
      (RingedSpace.modulePullbackDerived f.toShHom).mapIso
        ((pullback.inclusionIso g).app K) ≪≫
      (RingedSpace.modulePullbackDerived.compIso f.toShHom g.toShHom hPullback).app K.obj ≪≫
      ((pullback.inclusionIso (f ≫ g)).app K).symm)

/-- Naturality of the objectwise canonical `DerivedQCoh` pullback-composition comparison. -/
theorem pullbackCompAppIso_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
      f.toShHom g.toShHom)) {K L : DerivedQCoh Z} (k : K ⟶ L) :
    (pullback f).map ((pullback g).map k) ≫ (pullbackCompAppIso f g hPullback L).hom =
      (pullbackCompAppIso f g hPullback K).hom ≫ (pullback (f ≫ g)).map k := sorry

/-- The canonical composition isomorphism for pullback on `DerivedQCoh`. -/
noncomputable def pullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
      f.toShHom g.toShHom)) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents (pullbackCompAppIso f g hPullback)
    (fun k ↦ pullbackCompAppIso_naturality f g hPullback k)

/-- The canonical composition isomorphism for pushforward on `DerivedQCoh`, obtained as the
right-adjoint mate of `pullbackCompIso`. -/
noncomputable def pushforwardCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact (f ≫ g)] [QuasiSeparated (f ≫ g)]
    (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
      f.toShHom g.toShHom)) :
    pushforwardCohomologyIn f ⋙ pushforwardCohomologyIn g ≅
      pushforwardCohomologyIn (f ≫ g) :=
  (((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).ofNatIsoLeft
    (pullbackCompIso f g hPullback)).rightAdjointUniq
      (pullbackPushforwardAdjunction (f ≫ g))

/-- Compose chosen right adjoints to derived pushforward, transporting the composite
adjunction along the canonical pushforward-composition isomorphism. -/
noncomputable def compositeRightAdjunction {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact (f ≫ g)] [QuasiSeparated (f ≫ g)]
    (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
      f.toShHom g.toShHom))
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (b : DerivedQCoh Z ⥤ DerivedQCoh Y)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (bAdjunction : pushforwardCohomologyIn g ⊣ b) :
    pushforwardCohomologyIn (f ≫ g) ⊣ b ⋙ a :=
  (aAdjunction.comp bAdjunction).ofNatIsoLeft (pushforwardCompIso f g hPullback)

/-- Derived pullback carries the fixed-right tensor product to the tensor product of the
two derived pullbacks. -/
noncomputable def pullbackTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (K L : DerivedQCoh Y) :
    (pullback f).obj (tensorObj K L) ≅ tensorObj ((pullback f).obj K) ((pullback f).obj L) :=
  (ModuleDerived.quasicoherentProperty X).fullyFaithfulι.preimageIso
    ((pullback.inclusionIso f).app (tensorObj K L) ≪≫
      (RingedSpace.modulePullbackDerived f.toShHom).mapIso (tensorObjIsoTensor K L) ≪≫
      (Functor.Monoidal.μIso (RingedSpace.modulePullbackDerived f.toShHom) K.obj L.obj).symm ≪≫
      (((pullback.inclusionIso f).app K).symm ⊗ᵢ
        ((pullback.inclusionIso f).app L).symm) ≪≫
      (tensorObjIsoTensor ((pullback f).obj K) ((pullback f).obj L)).symm)

/-- Distribute the outer pullback over a tensor, identify iterated pullback with pullback
along the composite, and retain a fixed final tensor factor. -/
noncomputable def pullbackTensorCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
      f.toShHom g.toShHom)) (K : DerivedQCoh Z) (L : DerivedQCoh Y) (E : DerivedQCoh X) :
    tensorObj ((pullback f).obj (tensorObj ((pullback g).obj K) L)) E ≅
      tensorObj (tensorObj ((pullback (f ≫ g)).obj K) ((pullback f).obj L)) E :=
  (tensorRight E).mapIso (pullbackTensorIso f ((pullback g).obj K) L) ≪≫
    (tensorRight E).mapIso
      ((tensorRight ((pullback f).obj L)).mapIso ((pullbackCompIso f g hPullback).app K))

/-- Apply a morphism to the right factor of a derived tensor product. -/
noncomputable def tensorObjMapRight
    {X : Scheme.{u}}
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    (A : DerivedQCoh X) {B C : DerivedQCoh X} (m : B ⟶ C) :
    tensorObj A B ⟶ tensorObj A C :=
  ⟨(tensorObjIsoTensor A B).hom ≫ (𝟙 A.obj ⊗ₘ m.hom) ≫
    (tensorObjIsoTensor A C).inv⟩


/-- Reassociate a threefold derived tensor product and apply a morphism to the last two
factors. -/
noncomputable def tensorObjAssocMapRight {X : Scheme.{u}}
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    (A B C D : DerivedQCoh X) (m : tensorObj B C ⟶ D) :
    tensorObj (tensorObj A B) C ⟶ tensorObj A D :=
  ⟨(tensorObjIsoTensor (tensorObj A B) C).hom ≫
    ((tensorObjIsoTensor A B).hom ⊗ₘ 𝟙 C.obj) ≫
    (α_ A.obj B.obj C.obj).hom ≫
    (𝟙 A.obj ⊗ₘ ((tensorObjIsoTensor B C).inv ≫ m.hom)) ≫
    (tensorObjIsoTensor A D).inv⟩

/-- The tensor-duality comparison for a composite morphism agrees with the iterated
comparisons after the canonical pullback, tensor, reassociation, and adjunction maps. -/
@[stacks 0B6R]
theorem pullbackTensorDualityMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HomotopyTensorDescends Z.toRingedSpace] [TensorDescends Z.toRingedSpace]
    [IsLocalization Z.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom g.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (f ≫ g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived (f ≫ g).toShHom)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (b : DerivedQCoh Z ⥤ DerivedQCoh Y)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (bAdjunction : pushforwardCohomologyIn g ⊣ b) (K : DerivedQCoh Z) :
    (pullbackTensorCompIso f g
        (RingedSpace.modulePullbackDerived.compComparison_isIso f.toShHom g.toShHom)
        K (b.obj (structureSheaf Z)) (a.obj (structureSheaf Y))).hom ≫
        tensorObjAssocMapRight ((pullback (f ≫ g)).obj K)
          ((pullback f).obj (b.obj (structureSheaf Z))) (a.obj (structureSheaf Y))
          (a.obj (b.obj (structureSheaf Z)))
          (pullbackTensorDualityMap f a aAdjunction (b.obj (structureSheaf Z))) ≫
        pullbackTensorDualityMap (f ≫ g) (b ⋙ a)
          (compositeRightAdjunction f g
            (RingedSpace.modulePullbackDerived.compComparison_isIso
              f.toShHom g.toShHom)
            a b aAdjunction bAdjunction) K =
      pullbackTensorDualityMap f a aAdjunction
          (tensorObj ((pullback g).obj K) (b.obj (structureSheaf Z))) ≫
        a.map (pullbackTensorDualityMap g b bAdjunction K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
