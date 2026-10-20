module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalTypes
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.EtaleCover
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism
public import ReasLib.RingTheory.Topology.Noetherian.LocalMorphismProperty

/-!
# Local properties of locally Noetherian formal algebraic space morphisms

Properties of continuous maps of Noetherian adic rings can be tested by
compatible formal-spectrum presentations and affine étale charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A locally Noetherian formal algebraic space is locally countably indexed. -/
instance instIsLocallyCountablyIndexed {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace.IsLocallyNoetherian X] :
    IsLocallyCountablyIndexed X := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)

/-- A morphism of affine formal algebraic spaces corresponds to a morphism of
`WAdm^Noeth` with property `P` when there are Noetherian adic presentations of
source and target, together with a continuous `S`-algebra map `φ` satisfying
`P`, such that `f` is identified with `Spf(φ)` on weak-ideal stages. -/
def correspondsTo {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V) : Prop :=
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
                  ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J

/-- `correspondsTo P f` unpacks as Noetherian adic presentations of the affine
source and target together with a continuous `S`-algebra map `φ` satisfying
`P` that induces `f` on weak-ideal stages. -/
theorem correspondsTo_iff {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V) :
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
                      ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J :=
  sorry

namespace correspondsTo

variable {P}

/-- A continuous `S`-algebra map `φ` with `P φ`, together with compatible
`Spf` presentations of the affine source and target, witnesses
`correspondsTo P f`. -/
theorem of {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
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
                ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J) :
    correspondsTo P f := sorry

/-- `correspondsTo P f` supplies Noetherian adic presentations and a continuous
`S`-algebra map `φ` with `P φ` inducing `f`. -/
theorem spec {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : U ⟶ V} (h : correspondsTo P f) :
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
                    ((𝒮.bigAffineInclusion S).map t) ≫ cV.ι.app J :=
  sorry

end correspondsTo

variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y)

/-- Every commutative square of `f` against étale maps from affine formal
algebraic spaces has top arrow corresponding to a morphism of `WAdm^Noeth`
with property `P`. -/
def etaleAffineLocally : Prop :=
  ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
    ChosenBigFppfSite.etale pU →
      ChosenBigFppfSite.etale pV →
      CommSq q pU pV f → correspondsTo P q

/-- `etaleAffineLocally P f` means every étale affine-chart square over `f`
has top arrow corresponding to a morphism of `WAdm^Noeth` with property `P`. -/
theorem etaleAffineLocally_iff : etaleAffineLocally P f ↔
    ∀ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
      [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
      ChosenBigFppfSite.etale pU →
        ChosenBigFppfSite.etale pV →
        CommSq q pU pV f → correspondsTo P q :=
  sorry

namespace etaleAffineLocally

/-- A universal étale affine-chart correspondence witnesses
`etaleAffineLocally P f`. -/
theorem of (h : ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V],
    ChosenBigFppfSite.etale pU →
      ChosenBigFppfSite.etale pV →
      CommSq q pU pV f → correspondsTo P q) :
    etaleAffineLocally P f := sorry

/-- `etaleAffineLocally P f` tests `P` on the top arrow of every étale affine
chart square over `f`. -/
theorem spec (h : etaleAffineLocally P f)
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsAffineFormalAlgebraicSpace U] [IsAffineFormalAlgebraicSpace V]
    (hEtU : ChosenBigFppfSite.etale pU)
    (hEtV : ChosenBigFppfSite.etale pV)
    (sq : CommSq q pU pV f) :
    correspondsTo P q := sorry

end etaleAffineLocally

/-- There is an affine étale covering `{Y_ j ⟶ Y}` such that each fibre
product `Y_ j ×_Y X` admits an affine étale covering `{X_ ji ⟶ Y_ j ×_Y X}`
with each `X_ ji ⟶ Y_ j` corresponding to a morphism of `WAdm^Noeth` with
property `P`. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ j, Y_ j ⟶ Y),
    ChosenBigFppfSite.IsEtaleAffineCover π ∧
      ∀ j, ∃ (ι' : Type (max u v))
        (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f),
        ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f)

/-- `existsCoverOnTarget P f` unpacks as an affine étale covering of `Y`
and, for each chart, an affine étale covering of the fibre product with
`X` whose projections to the chart correspond to morphisms of `WAdm^Noeth`
with property `P`. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget P f ↔
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f) :=
  sorry

namespace existsCoverOnTarget

/-- An affine étale covering of `Y`, together with affine étale
coverings of each `Y_ j ×_Y X` whose projections to `Y_ j` correspond to
morphisms of `WAdm^Noeth` with property `P`, witnesses
`existsCoverOnTarget P f`. -/
theorem of {ι : Type (max u v)}
    {Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ j, Y_ j ⟶ Y) (hY : ChosenBigFppfSite.IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type (max u v))
      (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f),
      ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget P f := sorry

/-- `existsCoverOnTarget P f` supplies an affine étale covering of `Y`
and compatible affine étale coverings of the fibre products with `X`. -/
theorem spec (h : existsCoverOnTarget P f) :
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          ChosenBigFppfSite.IsEtaleAffineCover σ ∧ ∀ k, correspondsTo P (σ k ≫ pullback.fst (π j) f) :=
  sorry

end existsCoverOnTarget

/-- There is an affine étale covering `{X_ i ⟶ X}` such that each chart
factors as `X_ i ⟶ Y_ i ⟶ Y` with `Y_ i` an affine formal algebraic space,
`Y_ i ⟶ Y` representable by algebraic spaces and étale, and `X_ i ⟶ Y_ i`
corresponding to a morphism of `WAdm^Noeth` with property `P`. -/
def existsCoverOnSource : Prop :=
  ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X),
    ChosenBigFppfSite.IsEtaleAffineCover π ∧
      ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        IsAffineFormalAlgebraicSpace Y_i ∧
          ChosenBigFppfSite.etale p ∧
            π i ≫ f = q ≫ p ∧ correspondsTo P q

/-- `existsCoverOnSource P f` unpacks as an affine étale covering of `X`
whose charts factor through affine étale charts of `Y` by morphisms
corresponding to morphisms of `WAdm^Noeth` with property `P`. -/
theorem existsCoverOnSource_iff : existsCoverOnSource P f ↔
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            ChosenBigFppfSite.etale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q :=
  sorry

namespace existsCoverOnSource

/-- An affine étale covering of `X` with affine étale factorizations
through `Y` corresponding to morphisms of `WAdm^Noeth` with property `P`
witnesses `existsCoverOnSource P f`. -/
theorem of {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) (hX : ChosenBigFppfSite.IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      IsAffineFormalAlgebraicSpace Y_i ∧
        ChosenBigFppfSite.etale p ∧
          π i ≫ f = q ≫ p ∧ correspondsTo P q) :
    existsCoverOnSource P f := sorry

/-- `existsCoverOnSource P f` supplies an affine étale covering of `X`
and affine étale factorizations through `Y`. -/
theorem spec (h : existsCoverOnSource P f) :
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      ChosenBigFppfSite.IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            ChosenBigFppfSite.etale p ∧
              π i ≫ f = q ≫ p ∧ correspondsTo P q :=
  sorry

end existsCoverOnSource

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y)

/-- For a local property of continuous maps of Noetherian adic rings, universal
affine étale testing, testing on a target cover and covers of its pullbacks,
and testing on a source cover through affine étale target charts are equivalent. -/
theorem tfae (hP : Noetherian.IsLocalMorphismProperty P) :
    List.TFAE [etaleAffineLocally P f, existsCoverOnTarget P f,
      existsCoverOnSource P f] := sorry

/-- A local property of Noetherian adic ring maps holds on every affine étale
square if and only if it holds on a target cover and covers of its pullbacks. -/
theorem etaleAffineLocally_iff_existsCoverOnTarget
    (hP : Noetherian.IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnTarget P f := sorry

/-- A local property of Noetherian adic ring maps holds on every affine étale
square if and only if it holds on a source cover through affine étale target charts. -/
theorem etaleAffineLocally_iff_existsCoverOnSource
    (hP : Noetherian.IsLocalMorphismProperty P) :
    etaleAffineLocally P f ↔ existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
