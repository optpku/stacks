module

public import stacks_project.Chap59.Definition_59_33_2_EtaleLocalRing
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Lemma_67_34_3_FiberDimension
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Definition_100_12_3_Dimension

/-!
# Dimension identity along a smooth scheme atlas

For a locally Noetherian algebraic stack, the displayed local-ring dimension
identity along a smooth morphism from a scheme is the going-down relation on
the self 2-fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic space `R` with projections `s`, `t` and diagonal `e` represents
the self 2-fibre product of a 1-morphism `p : GroupoidsOver.slice U ⟶ X`. -/
def IsSelfFibreProduct {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) {R : AlgebraicSpace S}
    (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) : Prop :=
  ∃ eqv : TwoFibreProduct.apex.{u + 1, u, u + 1, u} p p ≌ R.toGroupoids,
    Nonempty
        (eqv.hom ≫ AlgebraicSpace.toGroupoids.map s ≫
            (AlgebraicSpace.ofOverSliceEquiv U).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} p p) ∧
      Nonempty
        (eqv.hom ≫ AlgebraicSpace.toGroupoids.map t ≫
            (AlgebraicSpace.ofOverSliceEquiv U).hom ≅
          TwoFibreProduct.snd.{u + 1, u, u + 1, u} p p) ∧
      Nonempty
        ((AlgebraicSpace.ofOverSliceEquiv U).hom ≫
            Hom.diagonal.{u + 1, u, u + 1} p ≫ eqv.hom ≅
          AlgebraicSpace.toGroupoids.map e)

/-- `IsSelfFibreProduct` means there is a bicategorical equivalence of `R` with
the self 2-fibre product of `p` identifying `s`, `t`, and `e` with
`TwoFibreProduct.fst`, `TwoFibreProduct.snd`, and `Hom.diagonal`. -/
theorem isSelfFibreProduct_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) {R : AlgebraicSpace S}
    (s t : R ⟶ AlgebraicSpace.ofOver U) (e : AlgebraicSpace.ofOver U ⟶ R) :
    IsSelfFibreProduct p s t e ↔
      ∃ eqv : TwoFibreProduct.apex.{u + 1, u, u + 1, u} p p ≌ R.toGroupoids,
        Nonempty
            (eqv.hom ≫ AlgebraicSpace.toGroupoids.map s ≫
                (AlgebraicSpace.ofOverSliceEquiv U).hom ≅
              TwoFibreProduct.fst.{u + 1, u, u + 1, u} p p) ∧
          Nonempty
            (eqv.hom ≫ AlgebraicSpace.toGroupoids.map t ≫
                (AlgebraicSpace.ofOverSliceEquiv U).hom ≅
              TwoFibreProduct.snd.{u + 1, u, u + 1, u} p p) ∧
          Nonempty
            ((AlgebraicSpace.ofOverSliceEquiv U).hom ≫
                Hom.diagonal.{u + 1, u, u + 1} p ≫ eqv.hom ≅
              AlgebraicSpace.toGroupoids.map e) :=
  sorry

/-- `IsSelfFibreProduct` yields the representing base change of `p` along `p`
together with the diagonal section identities for `s` and `t`. -/
theorem isSelfFibreProduct_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Over S} {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    RepresentsBaseChange p p R s ∧
      e ≫ s = 𝟙 (AlgebraicSpace.ofOver U) ∧
      e ≫ t = 𝟙 (AlgebraicSpace.ofOver U) :=
  sorry

namespace IsSelfFibreProduct

/-- A self fibre product representation of `p` yields `RepresentsBaseChange` for
the first projection. -/
theorem representsBaseChange {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    RepresentsBaseChange p p R s :=
  sorry

/-- The diagonal of a self fibre product is a section of the source projection. -/
theorem source {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    e ≫ s = 𝟙 (AlgebraicSpace.ofOver U) :=
  sorry

/-- The diagonal of a self fibre product is a section of the target projection. -/
theorem target {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    e ≫ t = 𝟙 (AlgebraicSpace.ofOver U) :=
  sorry

/-- The algebraic-space diagonal corresponds to `Hom.diagonal p` along the
representing equivalence. -/
theorem diagonal {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S}
    {p : GroupoidsOver.slice U ⟶ X} {R : AlgebraicSpace S}
    {s t : R ⟶ AlgebraicSpace.ofOver U} {e : AlgebraicSpace.ofOver U ⟶ R}
    (hR : IsSelfFibreProduct p s t e) :
    ∃ eqv : TwoFibreProduct.apex.{u + 1, u, u + 1, u} p p ≌ R.toGroupoids,
      Nonempty
        ((AlgebraicSpace.ofOverSliceEquiv U).hom ≫
            Hom.diagonal.{u + 1, u, u + 1} p ≫ eqv.hom ≅
          AlgebraicSpace.toGroupoids.map e) :=
  sorry

end IsSelfFibreProduct

/-- The Krull dimension of the étale local ring of a scheme at a geometric point
equals the dimension of the local ring of the associated algebraic space at the
image point. -/
theorem ringKrullDim_etaleLocalRing_eq_localRingDimAt {S : Scheme.{u}}
    (U : Over S) (ubar : Scheme.GeometricPoint U.left) :
    ringKrullDim (Scheme.etaleLocalRing U.left ubar) =
      AlgebraicSpace.localRingDimAt
        (AlgebraicSpace.ofOver.pointsEquiv U ubar.image) :=
  sorry

/-- Lemma 107.6.1: Let `X` be a locally Noetherian algebraic stack. Let
`p : GroupoidsOver.slice U ⟶ X` be a smooth morphism and let `u` be a point of
`U`. Then
`dimensionDiff (ringKrullDim (Scheme.etaleLocalRing U.left ubar))
  (AlgebraicSpace.fiberStalkDimAt s (Points.map e (ofOver.pointsEquiv U u)))`
equals
`dimensionDiff (d + d)
  (ringKrullDim (AlgebraicSpace.etaleLocalRing R ((ofScheme ubar).map e)))`,
where `d = ringKrullDim (Scheme.etaleLocalRing U.left ubar)`, the algebraic
space `R` represents the self 2-fibre product of `p` with projections `s`, `t`
and diagonal `e`, and the fibre of `s` over `u` is measured by
`fiberStalkDimAt`. -/
@[stacks 0DS8]
theorem smoothSelfFibre_etaleLocalRingDim_eq {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    {R : AlgebraicSpace S} (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) (hR : IsSelfFibreProduct p s t e)
    (u : U.left) (ubar : Scheme.GeometricPoint U.left) (hu : ubar.image = u) :
    dimensionDiff
        (ringKrullDim (Scheme.etaleLocalRing U.left ubar))
        (AlgebraicSpace.fiberStalkDimAt s
          (AlgebraicSpace.Points.map e (AlgebraicSpace.ofOver.pointsEquiv U u))) =
      dimensionDiff
        (ringKrullDim (Scheme.etaleLocalRing U.left ubar) +
          ringKrullDim (Scheme.etaleLocalRing U.left ubar))
        (ringKrullDim
          (AlgebraicSpace.etaleLocalRing R
            ((AlgebraicSpace.GeometricPoint.ofScheme ubar).map e))) :=
  sorry

/-- Going-down form of the identity: `ringKrullDim` of the étale local ring of
`R` at `e(ubar)` equals `ringKrullDim` of the étale local ring of `U` at `ubar`
plus `fiberStalkDimAt s` at `e(u)`. -/
theorem smoothSelfFibre_etaleLocalRingDim_add {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    {R : AlgebraicSpace S} (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) (hR : IsSelfFibreProduct p s t e)
    (u : U.left) (ubar : Scheme.GeometricPoint U.left) (hu : ubar.image = u) :
    ringKrullDim
        (AlgebraicSpace.etaleLocalRing R
          ((AlgebraicSpace.GeometricPoint.ofScheme ubar).map e)) =
      ringKrullDim (Scheme.etaleLocalRing U.left ubar) +
        AlgebraicSpace.fiberStalkDimAt s
          (AlgebraicSpace.Points.map e
            (AlgebraicSpace.ofOver.pointsEquiv U u)) :=
  sorry

/-- The identity in terms of `localRingDimAt` and `fiberStalkDimAt`, without a
chosen geometric point. -/
theorem smoothSelfFibre_localRingDimAt_eq {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    {R : AlgebraicSpace S} (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) (hR : IsSelfFibreProduct p s t e)
    (u : U.left) :
    dimensionDiff
        (AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u))
        (AlgebraicSpace.fiberStalkDimAt s
          (AlgebraicSpace.Points.map e (AlgebraicSpace.ofOver.pointsEquiv U u))) =
      dimensionDiff
        (AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u) +
          AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u))
        (AlgebraicSpace.localRingDimAt
          (AlgebraicSpace.Points.map e
            (AlgebraicSpace.ofOver.pointsEquiv U u))) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
