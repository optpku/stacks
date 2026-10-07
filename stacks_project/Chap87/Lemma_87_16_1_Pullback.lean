module

public import stacks_project.Chap87.Lemma_87_17_1_QuasiCompact

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
        IsQuasiCompact (pullback u v) := sorry

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
    forallQuasiCompactPullback X := sorry

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
    IsQuasiCompact (pullback u v) := sorry

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
    (hpb : IsPullback p q u v) : IsQuasiCompact P := sorry

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
        IsQuasiCompact (pullback u v) := sorry

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
    forallAffineQuasiCompactPullback X := sorry

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
    IsQuasiCompact (pullback u v) := sorry

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
    (hpb : IsPullback p q u v) : IsQuasiCompact P := sorry

end forallAffineQuasiCompactPullback

end AlgebraicGeometry.ChosenBigFppfSite
