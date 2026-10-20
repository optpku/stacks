module

public import stacks_project.Chap87.Lemma_87_16_4_Separated

/-!
# Affine fibre products of affine tests over a sheaf

Fibre products of morphisms from affine objects of a chosen big fppf site
into a sheaf may be tested for affinity together with surjectivity of the
induced `ℤ`-tensor map on global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

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
  sorry

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
  sorry

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
  sorry

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
      Function.Surjective (sectionTensor pW qW) :=
  sorry

end forallAffinePullbackAffineSurjective

end AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.IsSeparatedFormalAlgebraicSpace

/-- A sheaf is a separated formal algebraic space iff it is a formal algebraic
space and affine tests have affine fibre product with surjective
`sectionTensor`. -/
theorem iff_forallAffinePullbackAffineSurjective
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsSeparatedFormalAlgebraicSpace X ↔
      IsFormalAlgebraicSpace X ∧ forallAffinePullbackAffineSurjective X :=
  sorry

end AlgebraicGeometry.IsSeparatedFormalAlgebraicSpace
