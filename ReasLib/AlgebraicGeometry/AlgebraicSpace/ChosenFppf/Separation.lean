/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf

/-!
# Absolute separation on a chosen big fppf site

Affine pullback criteria for sheaves and algebraic spaces, using the canonical
`ℤ`-tensor map on global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

open scoped TensorProduct

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- The map `Γ(U, ⊤) ⊗[ℤ] Γ(V, ⊤) →+* Γ(W, ⊤)` induced by morphisms
`p : W ⟶ U` and `q : W ⟶ V` of affine objects of `(Sch/S)_fppf`. -/
def sectionTensor {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {U V W : 𝒮.bigAffineSite S} (p : W ⟶ U) (q : W ⟶ V) :
    Γ((𝒮.bigAffineToScheme S).obj U, ⊤) ⊗[ℤ]
        Γ((𝒮.bigAffineToScheme S).obj V, ⊤) →+*
      Γ((𝒮.bigAffineToScheme S).obj W, ⊤) :=
  (Algebra.TensorProduct.productMap
      ((𝒮.bigAffineToScheme S).map p).appTop.hom.toIntAlgHom
      ((𝒮.bigAffineToScheme S).map q).appTop.hom.toIntAlgHom).toRingHom

/-- `sectionTensor p q` is the `ℤ`-algebra product map of the global-section
maps of `p` and `q`. -/
theorem sectionTensor_eq {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {U V W : 𝒮.bigAffineSite S} (p : W ⟶ U) (q : W ⟶ V) :
    sectionTensor p q =
      (Algebra.TensorProduct.productMap
          ((𝒮.bigAffineToScheme S).map p).appTop.hom.toIntAlgHom
          ((𝒮.bigAffineToScheme S).map q).appTop.hom.toIntAlgHom).toRingHom :=
  rfl

namespace ChosenBigFppfSite

/-- Fibre products of morphisms from affine objects of `(Sch/S)_fppf` to `X`
are affine, and the induced map `Γ(U, ⊤) ⊗[ℤ] Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)` is
surjective. -/
def forallAffinePullbackAffineSurjective {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∀ (U V : 𝒮.bigAffineSite S)
    (u : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
    ∃ (W : 𝒮.bigAffineSite S) (p : W ⟶ U) (q : W ⟶ V)
      (e : pullback u v ≅ (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj W)),
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map p) =
        pullback.fst u v ∧
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map q) =
        pullback.snd u v ∧
      Function.Surjective (sectionTensor p q)

/-- `forallAffinePullbackAffineSurjective X` means that fibre products of
affine schemes over `X` are affine with surjective `sectionTensor`. -/
theorem forallAffinePullbackAffineSurjective_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    forallAffinePullbackAffineSurjective X ↔
      ∀ (U V : 𝒮.bigAffineSite S)
        (u : (𝒮.bigTopology S).sheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
        (v : (𝒮.bigTopology S).sheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
        ∃ (W : 𝒮.bigAffineSite S) (p : W ⟶ U) (q : W ⟶ V)
          (e : pullback u v ≅ (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj W)),
          e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
              ((𝒮.bigAffineInclusion S).map p) =
            pullback.fst u v ∧
          e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
              ((𝒮.bigAffineInclusion S).map q) =
            pullback.snd u v ∧
          Function.Surjective (sectionTensor p q) :=
  Iff.rfl

namespace forallAffinePullbackAffineSurjective

/-- The universal affine-scheme pullback condition witnesses
`forallAffinePullbackAffineSurjective X`. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : ∀ (U V : 𝒮.bigAffineSite S)
      (u : (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
      (v : (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
      ∃ (W : 𝒮.bigAffineSite S) (p : W ⟶ U) (q : W ⟶ V)
        (e : pullback u v ≅ (𝒮.bigTopology S).sheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj W)),
        e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
            ((𝒮.bigAffineInclusion S).map p) =
          pullback.fst u v ∧
        e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
            ((𝒮.bigAffineInclusion S).map q) =
          pullback.snd u v ∧
        Function.Surjective (sectionTensor p q)) :
    forallAffinePullbackAffineSurjective X :=
  h

/-- If `forallAffinePullbackAffineSurjective X`, then the chosen fibre product
of morphisms from affine schemes to `X` is affine with surjective
`sectionTensor`. -/
theorem apply {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : forallAffinePullbackAffineSurjective X) {U V : 𝒮.bigAffineSite S}
    (u : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V) ⟶ X) :
    ∃ (W : 𝒮.bigAffineSite S) (p : W ⟶ U) (q : W ⟶ V)
      (e : pullback u v ≅ (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj W)),
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map p) =
        pullback.fst u v ∧
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map q) =
        pullback.snd u v ∧
      Function.Surjective (sectionTensor p q) :=
  h U V u v

/-- If `forallAffinePullbackAffineSurjective X`, then any vertex of an
`IsPullback` square of morphisms from affine schemes to `X` is affine with
surjective `sectionTensor`. -/
theorem of_isPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X P : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : forallAffinePullbackAffineSurjective X) {U V : 𝒮.bigAffineSite S}
    {u : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U) ⟶ X}
    {v : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V) ⟶ X}
    {p : P ⟶ (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U)}
    {q : P ⟶ (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V)}
    (hpb : IsPullback p q u v) :
    ∃ (W : 𝒮.bigAffineSite S) (pW : W ⟶ U) (qW : W ⟶ V)
      (e : P ≅ (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj W)),
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map pW) =
        p ∧
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map qW) =
        q ∧
      Function.Surjective (sectionTensor pW qW) := by
  obtain ⟨W, pW, qW, e, hpW, hqW, hsurj⟩ := h U V u v
  refine ⟨W, pW, qW, hpb.isoPullback ≪≫ e, ?_, ?_, hsurj⟩
  · simpa only [Iso.trans_hom, Category.assoc, hpW] using hpb.isoPullback_hom_fst
  · simpa only [Iso.trans_hom, Category.assoc, hqW] using hpb.isoPullback_hom_snd

end forallAffinePullbackAffineSurjective


/-- A sheaf on `(Sch/S)_fppf` is a separated algebraic space when it is an
algebraic space and fibre products of morphisms from affine schemes to it
are affine with surjective `Γ(U, ⊤) ⊗[ℤ] Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)`. -/
class IsSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsAlgebraicSpace X where
  /-- Fibre products of morphisms from affine schemes to `X` are affine with
  surjective `sectionTensor`. -/
  affine_pullback_surjective : forallAffinePullbackAffineSurjective X

namespace IsSeparated

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is a
separated algebraic space. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsSeparated ((𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U)) where
  affine_pullback_surjective := sorry

/-- A sheaf is a separated algebraic space iff it is an algebraic space and
fibre products of morphisms from affine schemes to it are affine with
surjective `sectionTensor`. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsSeparated X ↔
      IsAlgebraicSpace X ∧ forallAffinePullbackAffineSurjective X := by
  exact ⟨fun h => ⟨h.toIsAlgebraicSpace, h.affine_pullback_surjective⟩,
    fun h => { toIsAlgebraicSpace := h.1, affine_pullback_surjective := h.2 }⟩

/-- A separated algebraic space unpacks as an algebraic space together with
affine fibre products of morphisms from affine schemes and surjective
`sectionTensor`. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsSeparated X] :
    IsAlgebraicSpace X ∧ forallAffinePullbackAffineSurjective X :=
  (iff X).mp inferInstance

/-- Affine fibre products of morphisms from affine schemes with surjective
`sectionTensor` witness that an algebraic space sheaf is separated. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsAlgebraicSpace X]
    (h : forallAffinePullbackAffineSurjective X) : IsSeparated X :=
  { toIsAlgebraicSpace := inferInstance, affine_pullback_surjective := h }

end IsSeparated


end ChosenBigFppfSite

end AlgebraicGeometry
