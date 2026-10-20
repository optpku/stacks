/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NoetherianLocalMorphismProperty

/-!
# Noetherian affine étale local tests

Typed compatibility checks for the Noetherian correspondence and chart tests.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.correspondsTo.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V),
    Prop)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.correspondsTo_iff.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V),
    correspondsTo P f ↔
      ∃ (A B : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : IsAdicRing A) (_ : IsNoetherianRing A)
        (_ : CommRing B) (_ : TopologicalSpace B)
        (_ : IsAdicRing B) (_ : IsNoetherianRing B)
        (hA : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
        (hB : Spec (.of B) ⟶ 𝒮.toScheme.obj S)
        (φ : B →+* A) (_ : Continuous φ)
        (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
        (DU : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
        (eU : ∀ I, (𝒮.bigAffineToScheme S).obj (DU.obj I) ≅ (stage A hA I).left)
        (cU : Cocone (DU ⋙ 𝒮.bigAffineInclusion S ⋙
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
        (iU : U ≅ cU.pt)
        (DV : WeakIdealOfDefinition B ⥤ 𝒮.bigAffineSite S)
        (eV : ∀ J, (𝒮.bigAffineToScheme S).obj (DV.obj J) ≅ (stage B hB J).left)
        (cV : Cocone (DV ⋙ 𝒮.bigAffineInclusion S ⋙
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
        (iV : V ≅ cV.pt),
        P φ ∧ Nonempty (IsColimit cU) ∧ Nonempty (IsColimit cV) ∧
          (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
            (eU I).hom ≫ ((thickenings A hA).map g).left =
              (𝒮.bigAffineToScheme S).map (DU.map g) ≫ (eU J).hom) ∧
          (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
            (eV I).hom ≫ ((thickenings B hB).map g).left =
              (𝒮.bigAffineToScheme S).map (DV.map g) ≫ (eV J).hom) ∧
          (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
            IsThickening ((𝒮.bigAffineToScheme S).map (DU.map g))) ∧
          (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
            IsThickening ((𝒮.bigAffineToScheme S).map (DV.map g))) ∧
          ∀ (I : WeakIdealOfDefinition A) (J : WeakIdealOfDefinition B)
            (hIJ : J.ideal ≤ Ideal.comap φ I.ideal),
            ∃ t : DU.obj I ⟶ DV.obj J,
              CommSq ((𝒮.bigAffineToScheme S).map t) (eU I).hom (eV J).hom
                  (stageMap φ h_over hIJ).left ∧
                cU.ι.app I ≫ iU.inv ≫ f ≫ iV.hom =
                  (𝒮.bigTopology S).sheafifiedRepresentableMap
                      ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.correspondsTo.of.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop}
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : U ⟶ V} {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (hA : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
    (hB : Spec (.of B) ⟶ 𝒮.toScheme.obj S)
    (φ : B →+* A) (hφ : Continuous φ)
    (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
    (hPφ : P φ)
    (DU : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
    (eU : ∀ I, (𝒮.bigAffineToScheme S).obj (DU.obj I) ≅ (stage A hA I).left)
    (cU : Cocone (DU ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (iU : U ≅ cU.pt)
    (DV : WeakIdealOfDefinition B ⥤ 𝒮.bigAffineSite S)
    (eV : ∀ J, (𝒮.bigAffineToScheme S).obj (DV.obj J) ≅ (stage B hB J).left)
    (cV : Cocone (DV ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (iV : V ≅ cV.pt)
    (hcU : Nonempty (IsColimit cU)) (hcV : Nonempty (IsColimit cV))
    (hDU : ∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
      (eU I).hom ≫ ((thickenings A hA).map g).left =
        (𝒮.bigAffineToScheme S).map (DU.map g) ≫ (eU J).hom)
    (hDV : ∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
      (eV I).hom ≫ ((thickenings B hB).map g).left =
        (𝒮.bigAffineToScheme S).map (DV.map g) ≫ (eV J).hom)
    (hThU : ∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
      IsThickening ((𝒮.bigAffineToScheme S).map (DU.map g)))
    (hThV : ∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
      IsThickening ((𝒮.bigAffineToScheme S).map (DV.map g)))
    (hMap : ∀ (I : WeakIdealOfDefinition A) (J : WeakIdealOfDefinition B)
      (hIJ : J.ideal ≤ Ideal.comap φ I.ideal),
      ∃ t : DU.obj I ⟶ DV.obj J,
        CommSq ((𝒮.bigAffineToScheme S).map t) (eU I).hom (eV J).hom
            (stageMap φ h_over hIJ).left ∧
          cU.ι.app I ≫ iU.inv ≫ f ≫ iV.hom =
            (𝒮.bigTopology S).sheafifiedRepresentableMap
                ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J),
    correspondsTo P f)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.correspondsTo.spec.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop}
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : U ⟶ V} (h : correspondsTo P f),
    ∃ (A B : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsAdicRing A) (_ : IsNoetherianRing A)
      (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : IsAdicRing B) (_ : IsNoetherianRing B)
      (hA : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
      (hB : Spec (.of B) ⟶ 𝒮.toScheme.obj S)
      (φ : B →+* A) (_ : Continuous φ)
      (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
      (DU : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
      (eU : ∀ I, (𝒮.bigAffineToScheme S).obj (DU.obj I) ≅ (stage A hA I).left)
      (cU : Cocone (DU ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
      (iU : U ≅ cU.pt)
      (DV : WeakIdealOfDefinition B ⥤ 𝒮.bigAffineSite S)
      (eV : ∀ J, (𝒮.bigAffineToScheme S).obj (DV.obj J) ≅ (stage B hB J).left)
      (cV : Cocone (DV ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
      (iV : V ≅ cV.pt),
      P φ ∧ Nonempty (IsColimit cU) ∧ Nonempty (IsColimit cV) ∧
        (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
          (eU I).hom ≫ ((thickenings A hA).map g).left =
            (𝒮.bigAffineToScheme S).map (DU.map g) ≫ (eU J).hom) ∧
        (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
          (eV I).hom ≫ ((thickenings B hB).map g).left =
            (𝒮.bigAffineToScheme S).map (DV.map g) ≫ (eV J).hom) ∧
        (∀ {I J : WeakIdealOfDefinition A} (g : I ⟶ J),
          IsThickening ((𝒮.bigAffineToScheme S).map (DU.map g))) ∧
        (∀ {I J : WeakIdealOfDefinition B} (g : I ⟶ J),
          IsThickening ((𝒮.bigAffineToScheme S).map (DV.map g))) ∧
        ∀ (I : WeakIdealOfDefinition A) (J : WeakIdealOfDefinition B)
          (hIJ : J.ideal ≤ Ideal.comap φ I.ideal),
          ∃ t : DU.obj I ⟶ DV.obj J,
            CommSq ((𝒮.bigAffineToScheme S).map t) (eU I).hom (eV J).hom
                (stageMap φ h_over hIJ).left ∧
              cU.ι.app I ≫ iU.inv ≫ f ≫ iV.hom =
                (𝒮.bigTopology S).sheafifiedRepresentableMap
                    ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
,
    Prop)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally_iff.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
,
    etaleAffineLocally P f ↔
    ∀ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
      [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
      ChosenBigFppfSite.etale pU →
        ChosenBigFppfSite.etale pV →
        CommSq q pU pV f → correspondsTo P q)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally.of.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
    (h : ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
    ChosenBigFppfSite.etale pU →
      ChosenBigFppfSite.etale pV →
      CommSq q pU pV f → correspondsTo P q),
    etaleAffineLocally P f)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally.spec.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
    (h : etaleAffineLocally P f)
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V]
    (hEtU : ChosenBigFppfSite.etale pU)
    (hEtV : ChosenBigFppfSite.etale pV)
    (sq : CommSq q pU pV f),
    correspondsTo P q)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnTarget.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
,
    Prop)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnTarget_iff.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
,
    existsCoverOnTarget P f ↔
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f))

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnTarget.of.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
    {ι : Type (max u v)}
    {Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ j, Y_ j ⟶ Y) (hY : ChosenBigFppfSite.IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type (max u v))
      (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f),
      ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f)),
    existsCoverOnTarget P f)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnTarget.spec.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
    (h : existsCoverOnTarget P f),
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f))

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnSource.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
,
    Prop)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnSource_iff.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
,
    existsCoverOnSource P f ↔
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            ChosenBigFppfSite.etale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnSource.of.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
    {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) (hX : ChosenBigFppfSite.IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      IsAffineFormalAlgebraicSpace Y_i ∧
        ChosenBigFppfSite.etale p ∧
          π i ≫ f = q ≫ p ∧ correspondsTo P q),
    existsCoverOnSource P f)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnSource.spec.{u, v} :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y)
    (h : existsCoverOnSource P f),
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            ChosenBigFppfSite.etale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q)

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
