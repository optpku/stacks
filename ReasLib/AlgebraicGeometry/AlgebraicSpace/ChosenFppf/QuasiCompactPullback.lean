/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.QuasiCompact

/-!
# Quasi-compact fibre products of schemes over a sheaf

Fibre products of morphisms from quasi-compact or affine objects of a chosen
big fppf site into a sheaf may be tested for quasi-compactness in the sheaf
category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- Quasi-compactness is preserved by an isomorphism of sheaves. -/
theorem IsQuasiCompact.of_iso {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsQuasiCompact X] (e : X ≅ Y) : IsQuasiCompact Y := by
  have hdiag :=
    ((𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable.arrow_mk_iso_iff
      (Arrow.isoMk' (diag X) (diag Y) e (prod.mapIso e e)
        (by simp only [prod.mapIso_hom, prod.diag_map]))).1
      (IsAlgebraicSpace.representableDiagonal (X := X))
  obtain ⟨U, p, hp, hs, hU⟩ := IsQuasiCompact.exists_compact_etaleCover (X := X)
  have hp' : relativelyEtale (p ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp
      ((MorphismProperty.inverseImage (@Etale) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor) e.hom p hp
  letI : Sheaf.IsLocallySurjective p := hs
  exact
    { toIsAlgebraicSpace :=
        { representableDiagonal := hdiag
          atlas := ⟨U, p ≫ e.hom, hp', inferInstance⟩ }
      exists_compact_etaleCover := ⟨U, p ≫ e.hom, hp', inferInstance, hU⟩ }

/-- Fibre products of morphisms from quasi-compact objects of `(Sch/S)_fppf` to
`X` are quasi-compact algebraic spaces. -/
def forallQuasiCompactPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∀ (U V : 𝒮.bigSite S)
    [CompactSpace ((𝒮.bigToScheme S).obj U)]
    [CompactSpace ((𝒮.bigToScheme S).obj V)]
    (u : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X),
    IsQuasiCompact (pullback u v)

/-- `forallQuasiCompactPullback X` means that fibre products of quasi-compact
schemes over `X` are quasi-compact. -/
theorem forallQuasiCompactPullback_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    forallQuasiCompactPullback X ↔
      ∀ (U V : 𝒮.bigSite S)
        [CompactSpace ((𝒮.bigToScheme S).obj U)]
        [CompactSpace ((𝒮.bigToScheme S).obj V)]
        (u : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
        (v : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X),
        IsQuasiCompact (pullback u v) := Iff.rfl

namespace forallQuasiCompactPullback

/-- The universal quasi-compact-scheme pullback condition witnesses
`forallQuasiCompactPullback X`. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : ∀ (U V : 𝒮.bigSite S)
      [CompactSpace ((𝒮.bigToScheme S).obj U)]
      [CompactSpace ((𝒮.bigToScheme S).obj V)]
      (u : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
      (v : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X),
      IsQuasiCompact (pullback u v)) :
    forallQuasiCompactPullback X := h

/-- If `forallQuasiCompactPullback X`, then the chosen fibre product of
morphisms from quasi-compact schemes to `X` is quasi-compact. -/
theorem apply {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : forallQuasiCompactPullback X) {U V : 𝒮.bigSite S}
    [CompactSpace ((𝒮.bigToScheme S).obj U)]
    [CompactSpace ((𝒮.bigToScheme S).obj V)]
    (u : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) :
    IsQuasiCompact (pullback u v) := h U V u v

/-- If `forallQuasiCompactPullback X`, then any vertex of an `IsPullback`
square of morphisms from quasi-compact schemes to `X` is quasi-compact. -/
theorem of_isPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X P : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : forallQuasiCompactPullback X) {U V : 𝒮.bigSite S}
    [CompactSpace ((𝒮.bigToScheme S).obj U)]
    [CompactSpace ((𝒮.bigToScheme S).obj V)]
    {u : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X}
    {v : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X}
    {p : P ⟶ (𝒮.bigTopology S).sheafifiedRepresentable U}
    {q : P ⟶ (𝒮.bigTopology S).sheafifiedRepresentable V}
    (hpb : IsPullback p q u v) : IsQuasiCompact P := by
  letI : IsQuasiCompact (pullback u v) := h U V u v
  exact IsQuasiCompact.of_iso hpb.isoPullback.symm

end forallQuasiCompactPullback

/-- Fibre products of morphisms from affine objects of `(Sch/S)_fppf` to `X`
are quasi-compact algebraic spaces. -/
def forallAffineQuasiCompactPullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∀ (U V : 𝒮.bigAffineSite S)
    (u : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
    IsQuasiCompact (pullback u v)

/-- `forallAffineQuasiCompactPullback X` means that fibre products of affine
schemes over `X` are quasi-compact. -/
theorem forallAffineQuasiCompactPullback_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    forallAffineQuasiCompactPullback X ↔
      ∀ (U V : 𝒮.bigAffineSite S)
        (u : (𝒮.bigTopology S).sheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
        (v : (𝒮.bigTopology S).sheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
        IsQuasiCompact (pullback u v) := Iff.rfl

namespace forallAffineQuasiCompactPullback

/-- The universal affine-scheme pullback condition witnesses
`forallAffineQuasiCompactPullback X`. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : ∀ (U V : 𝒮.bigAffineSite S)
      (u : (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
      (v : (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
      IsQuasiCompact (pullback u v)) :
    forallAffineQuasiCompactPullback X := h

/-- If `forallAffineQuasiCompactPullback X`, then the chosen fibre product of
morphisms from affine schemes to `X` is quasi-compact. -/
theorem apply {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : forallAffineQuasiCompactPullback X) {U V : 𝒮.bigAffineSite S}
    (u : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V) ⟶ X) :
    IsQuasiCompact (pullback u v) := h U V u v

/-- If `forallAffineQuasiCompactPullback X`, then any vertex of an `IsPullback`
square of morphisms from affine schemes to `X` is quasi-compact. -/
theorem of_isPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X P : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : forallAffineQuasiCompactPullback X) {U V : 𝒮.bigAffineSite S}
    {u : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U) ⟶ X}
    {v : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V) ⟶ X}
    {p : P ⟶ (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U)}
    {q : P ⟶ (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V)}
    (hpb : IsPullback p q u v) : IsQuasiCompact P := by
  letI : IsQuasiCompact (pullback u v) := h U V u v
  exact IsQuasiCompact.of_iso hpb.isoPullback.symm

end forallAffineQuasiCompactPullback

end AlgebraicGeometry.ChosenBigFppfSite
