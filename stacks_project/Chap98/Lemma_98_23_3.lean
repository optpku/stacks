module

public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Definition_98_23_5_AffineOpen
public import stacks_project.Chap98.Lemma_98_23_2_Comparison
public import stacks_project.Chap98.Lemma_98_23_3_Cotangent
public import stacks_project.Chap98.Remark_98_21_8_Canonical_element_Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 98.23.3

A morphism `ξ : E ⟶ NL{A⁄Λ}` that detects lifts of `x` and matches the
canonical element of `T_x` characterizes versality at a finite type point
`u0` by the homology of `ξ ⊗^L κ(u0)`.
-/

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

/-- Condition (i): `x` lifts to `Spec(A')` if and only if
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

/-- An isomorphism of functors `T_x(-) ≅ Ext^0_A(E, -)`. -/
abbrev tangentExtIso :=
  tangentFunctor ξ.toObjectOverSpec.toFiber ≅
    DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ)

/-- Comparison of `kaehlerObj` of the bundled algebra map with the unbundled
Kähler module `Ω[A⁄Λ]`. -/
theorem kaehlerObj_eq_unbundled :
    kaehlerObj ξ.algebraHom =
      ModuleCat.of ξ.carrier Ω[ξ.carrier ⁄ ξ.base] :=
  sorry

/-- Condition (ii): the functor isomorphism identifies the canonical element
with the Ext class of `E ⟶ NL{A⁄Λ} ⟶ Ω[A⁄Λ]`. -/
def matchesCanonical
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ)) : Prop :=
  iso.hom.app (kaehlerObj ξ.algebraHom)
      (canonicalElement ξ.algebraHom ξ.factor ξ.toObjectOverSpec.toFiber
        ξ.isOpenImmersion) =
    eqToHom
      (congrArg
        (fun M ↦ (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ)).obj M)
        kaehlerObj_eq_unbundled.symm)
      (Algebra.NaiveCotangent.extObjOfHom
        (obstructionMap ≫ Algebra.NaiveCotangent.naiveCotangentToKaehler))

/-- Unfolding of `matchesCanonical` as an equality of Ext classes after
transport along `kaehlerObj_eq`. -/
theorem matchesCanonical_iff
    (iso : tangentFunctor ξ.toObjectOverSpec.toFiber ≅
      DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ)) :
    matchesCanonical obstructionMap iso ↔
      iso.hom.app (kaehlerObj ξ.algebraHom)
          (canonicalElement ξ.algebraHom ξ.factor ξ.toObjectOverSpec.toFiber
            ξ.isOpenImmersion) =
        eqToHom
          (congrArg
            (fun M ↦
              (DerivedCategory.Ext.moduleFunctor (Minus.ι.obj E) (0 : ℤ)).obj M)
            kaehlerObj_eq_unbundled.symm)
          (Algebra.NaiveCotangent.extObjOfHom
            (obstructionMap ≫ Algebra.NaiveCotangent.naiveCotangentToKaehler)) :=
  sorry

variable (u0 : Spec (CommRingCat.of ξ.carrier))
variable [IsFiniteTypePoint u0]

section ResidueHomology

variable (k : Type u) [Field k] [Algebra ξ.carrier k]

/-- The homology map of `ξ ⊗^L k` in degree `i`. -/
def homologyMapAt (i : ℤ) :
    (homologyFunctor (ModuleCat k) i).obj
      ((ModuleCat.derivedExtensionOfScalars (algebraMap ξ.carrier k)).obj
        (Minus.ι.obj E)) ⟶
    (homologyFunctor (ModuleCat k) i).obj
      ((ModuleCat.derivedExtensionOfScalars (algebraMap ξ.carrier k)).obj
        (Algebra.naiveCotangentObject ξ.base ξ.carrier)) :=
  Algebra.NaiveCotangent.homologyMap obstructionMap i

/-- `homologyMapAt i` is `homologyMap` of the obstruction morphism in degree
`i`. -/
theorem homologyMapAt_eq (i : ℤ) :
    homologyMapAt obstructionMap k i =
      Algebra.NaiveCotangent.homologyMap obstructionMap i :=
  sorry

/-- The homology criterion at `k`: `H⁻¹(ξ ⊗^L k)` is surjective and
`H⁰(ξ ⊗^L k)` is injective. -/
structure HomologyCriterion : Prop where
  /-- Surjectivity of `H⁻¹(ξ ⊗^L k)`. -/
  surjective_negOne : Epi (homologyMapAt obstructionMap k (-1))
  /-- Injectivity of `H⁰(ξ ⊗^L k)`. -/
  injective_zero : Mono (homologyMapAt obstructionMap k 0)

/-- Package the two homology maps of `ξ ⊗^L k` as a homology criterion. -/
def HomologyCriterion.of
    (h_neg : Epi (homologyMapAt obstructionMap k (-1)))
    (h_zero : Mono (homologyMapAt obstructionMap k 0)) :
    HomologyCriterion obstructionMap k where
  surjective_negOne := h_neg
  injective_zero := h_zero

/-- The homology criterion is equivalent to surjectivity in degree `-1` and
injectivity in degree `0`. -/
theorem HomologyCriterion.iff :
    HomologyCriterion obstructionMap k ↔
      Epi (homologyMapAt obstructionMap k (-1)) ∧
        Mono (homologyMapAt obstructionMap k 0) :=
  sorry

end ResidueHomology

/-- Lemma 98.23.3 (1). Let `S` be a locally Noetherian scheme. Let `X` be a
category fibred in groupoids over `(Sch/S)_fppf` satisfying (RS*). Let
`U = Spec(A)` be an affine scheme of finite type over `S` which maps into an
affine open `Spec(Λ)`. Let `x` be an object of `X` over `U`. Let
`ξ : E ⟶ NL{A⁄Λ}` be a morphism of `D⁻(A)`. Assume (i) for every deformation
situation `(x, A' → A)`, `x` lifts to `Spec(A')` if and only if
`E ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'}` is zero, and (ii) there is an isomorphism of
functors `T_x(-) ⟶ Ext^0_A(E, -)` such that
`E ⟶ NL{A⁄Λ} ⟶ Ω[A⁄Λ]` corresponds to the canonical element. Let `u0 ∈ U`
be a finite type point with residue field `k = κ(u0)`. If `ξ` induces a
surjection `H⁻¹(E ⊗^L_A k) ⟶ H⁻¹(NL{A⁄Λ} ⊗^L_A k)` and an injection
`H⁰(E ⊗^L_A k) ⟶ H⁰(NL{A⁄Λ} ⊗^L_A k)`, then `x` is versal at `u0`. -/
@[stacks 07YM]
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

/-- Lemma 98.23.3 (2). In the same setting as Lemma 98.23.3 (1), if `u0` is a
closed point and `x` is versal at `u0`, then `ξ` induces a surjection
`H⁻¹(E ⊗^L_A k) ⟶ H⁻¹(NL{A⁄Λ} ⊗^L_A k)` and an injection
`H⁰(E ⊗^L_A k) ⟶ H⁰(NL{A⁄Λ} ⊗^L_A k)`. -/
@[stacks 07YM]
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
