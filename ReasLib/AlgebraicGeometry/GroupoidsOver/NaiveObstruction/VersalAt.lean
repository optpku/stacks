module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObjectOverAffineOpen
public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalElement
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Functor
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.SquareZeroComparison
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Augmentation
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Homology

/-! # Versality criteria from individual naive obstruction morphisms -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open Algebra
open DerivedCategory
open scoped NaiveCotangent

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
variable {ξ : ObjectOverAffineOpen X} [LocallyOfFiniteType ξ.toS]
variable {E : Minus (ModuleCat.{u} ξ.carrier)}
variable (obstructionMap :
    Minus.ι.obj E ⟶ Algebra.naiveCotangentObject ξ.base ξ.carrier)

/-- The composite `E ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'}` along a square-zero thickening of
`x` over the affine open `Spec(Λ)`. -/
def obstructionComposite (τ : DeformationSituation.OverAffine ξ) :=
  obstructionMap ≫
    @Algebra.NaiveCotangent.naiveCotangentMap ξ.base τ.situation.source
      ξ.carrier _ _ _ τ.algebra ξ.algebra τ.algHom

/-- `obstructionComposite` is `obstructionMap` followed by
`naiveCotangentMap` of the thickening. -/
theorem obstructionComposite_eq (τ : DeformationSituation.OverAffine ξ) :
    obstructionComposite obstructionMap τ =
      obstructionMap ≫
        @Algebra.NaiveCotangent.naiveCotangentMap ξ.base τ.situation.source
          ξ.carrier _ _ _ τ.algebra ξ.algebra τ.algHom :=
  sorry

/-- The object `x` lifts to `Spec(A')` if and only if
`E ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'}` vanishes. -/
def detectsLifts : Prop :=
  ∀ τ : DeformationSituation.OverAffine ξ,
    obstructionComposite obstructionMap τ = 0 ↔
      Nonempty (DeformationSituation.ObjectLift τ.situation)

/-- Unfolding of `detectsLifts` into the vanishing criterion for lifts. -/
theorem detectsLifts_iff :
    detectsLifts obstructionMap ↔
      ∀ τ : DeformationSituation.OverAffine ξ,
        obstructionComposite obstructionMap τ = 0 ↔
          Nonempty (DeformationSituation.ObjectLift τ.situation) :=
  sorry

/-- The tangent-to-Ext isomorphism sends the canonical tangent element,
after the canonical comparison of Kähler differentials, to the augmented
obstruction morphism. -/
def matchesCanonical
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ)) : Prop :=
  (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ)).map
        (ObjectOverAffineOpen.kaehlerCompare ξ)
      (iso.hom.app (CommRingCat.KaehlerDifferential ξ.algebraHom)
        (canonicalElement ξ.algebraHom ξ.factor ξ.toObjectOverSpec.toFiber
          ξ.isOpenImmersion)) =
    ShiftedHom.mk₀ (0 : ℤ) rfl
      (obstructionMap ≫ Algebra.NaiveCotangent.naiveCotangentToKaehler)

/-- Compatibility with the canonical tangent element is the equality between
its transported Ext class and the augmented obstruction morphism. -/
theorem matchesCanonical_iff
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ)) :
    matchesCanonical obstructionMap iso ↔
      (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ)).map
            (ObjectOverAffineOpen.kaehlerCompare ξ)
          (iso.hom.app (CommRingCat.KaehlerDifferential ξ.algebraHom)
            (canonicalElement ξ.algebraHom ξ.factor ξ.toObjectOverSpec.toFiber
              ξ.isOpenImmersion)) =
        ShiftedHom.mk₀ (0 : ℤ) rfl
          (obstructionMap ≫ Algebra.NaiveCotangent.naiveCotangentToKaehler) :=
  sorry

variable (u0 : Spec (CommRingCat.of ξ.carrier))
variable [IsFiniteTypePoint u0]

section ResidueHomology

variable (k : Type u) [Field k] [Algebra ξ.carrier k]

/-- The homology criterion at `k`: `H⁻¹(ξ ⊗^L k)` is surjective and
`H⁰(ξ ⊗^L k)` is injective. -/
structure HomologyCriterion : Prop where
  /-- Surjectivity of `H⁻¹(ξ ⊗^L k)`. -/
  surjective_negOne : Epi (Algebra.NaiveCotangent.homologyMap (k := k) obstructionMap (-1))
  /-- Injectivity of `H⁰(ξ ⊗^L k)`. -/
  injective_zero : Mono (Algebra.NaiveCotangent.homologyMap (k := k) obstructionMap 0)

/-- Package the two homology maps of `ξ ⊗^L k` as a homology criterion. -/
def HomologyCriterion.of
    (h_neg : Epi (Algebra.NaiveCotangent.homologyMap (k := k) obstructionMap (-1)))
    (h_zero : Mono (Algebra.NaiveCotangent.homologyMap (k := k) obstructionMap 0)) :
    HomologyCriterion obstructionMap k where
  surjective_negOne := h_neg
  injective_zero := h_zero

/-- The homology criterion is equivalent to surjectivity in degree `-1` and
injectivity in degree `0`. -/
theorem HomologyCriterion.iff :
    HomologyCriterion obstructionMap k ↔
      Epi (Algebra.NaiveCotangent.homologyMap (k := k) obstructionMap (-1)) ∧
        Mono (Algebra.NaiveCotangent.homologyMap (k := k) obstructionMap 0) :=
  sorry

end ResidueHomology

/-- For an affine finite-type object over a locally Noetherian base satisfying
(RS*), an obstruction morphism detecting lifts and matching the canonical
tangent element gives versality at a finite type point if its residue homology
map is surjective in degree `-1` and injective in degree `0`. -/
theorem isVersalAt_of_homology
    [Algebra ξ.carrier (residueFieldType u0)]
    (hπ :
      Spec.map (CommRingCat.ofHom
          (algebraMap ξ.carrier (residueFieldType u0))) =
        fromResidueField u0)
    (h_lifts : detectsLifts obstructionMap)
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ))
    (h_canonical : matchesCanonical obstructionMap iso)
    (h_hom : HomologyCriterion obstructionMap (residueFieldType u0)) :
    IsVersalAt ξ.toS ξ.obj ξ.over_obj u0 :=
  sorry

/-- At a closed finite type point, versality of an affine finite-type object
over a locally Noetherian base satisfying (RS*) forces an obstruction morphism
detecting lifts and matching the canonical tangent element to be surjective
on residue homology in degree `-1` and injective in degree `0`. -/
theorem homologyCriterion_of_isVersalAt
    [Algebra ξ.carrier (residueFieldType u0)]
    (hπ :
      Spec.map (CommRingCat.ofHom
          (algebraMap ξ.carrier (residueFieldType u0))) =
        fromResidueField u0)
    (h_lifts : detectsLifts obstructionMap)
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ))
    (h_canonical : matchesCanonical obstructionMap iso)
    [IsVersalAt ξ.toS ξ.obj ξ.over_obj u0]
    (h_closed : IsClosed {u0}) :
    HomologyCriterion obstructionMap (residueFieldType u0) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
