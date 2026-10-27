/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.AffineSpace.AdditiveGroup
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Variety.AffinePresentation

/-!
# The affine-line involution algebraic space

The affine line `U = 𝔸¹_k` over `Spec k` has a relation `j : Δ ⨿ Γ ⟶ U ×_k U` whose
first summand is the relative diagonal and whose second summand is the graph of `x ↦ -x`
on `D(x)`. Its fppf quotient sheaf has the canonical quotient map as an atlas. In
characteristic different from two, the quotient is an algebraic space that is
quasi-separated but not locally separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The index type of the relation scheme: `false` for the diagonal summand `Δ`, and `true`
for the graph summand `Γ`. -/
abbrev relationIndex : Type := Bool

/-- The relation index is the boolean with `false` for `Δ` and `true` for `Γ`. -/
theorem relationIndex_eq : relationIndex = Bool := rfl

/-- The relation index is `u`-small, so the coproduct of relation summands exists in `Scheme`. -/
instance instSmallRelationIndex : Small.{u} relationIndex := inferInstance

/-- The base scheme `Spec k`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of.{u} k)

/-- The base scheme is the spectrum of `k`. -/
theorem base_eq (k : Type u) [Field k] : base k = Spec (CommRingCat.of.{u} k) := rfl

/-- The affine line `U = 𝔸¹_k` as a scheme over `Spec k`. -/
def cover (k : Type u) [Field k] : Over (base k) :=
  Over.mk (affineSpaceOverFieldHom k 1)

/-- The underlying scheme of the cover is affine 1-space over `k`. -/
theorem cover_left (k : Type u) [Field k] :
    (cover k).left = AffineSpaceOverField k 1 := rfl

/-- The structure morphism of the cover is the canonical map `𝔸¹_k ⟶ Spec k`. -/
theorem cover_hom (k : Type u) [Field k] :
    (cover k).hom = affineSpaceOverFieldHom k 1 := rfl

/-- Coordinatewise negation `x ↦ -x` on the affine line, as a morphism over `Spec k`. -/
def involution (k : Type u) [Field k] : cover k ⟶ cover k :=
  Over.homMk (AffineSpace.negLeft (ULift.{u} (Fin 1)) (base k))
    (AffineSpace.negHom_w (ULift.{u} (Fin 1)) (base k))

/-- The underlying scheme map of the involution is coordinatewise negation. -/
theorem involution_left (k : Type u) [Field k] :
    (involution k).left = AffineSpace.negLeft (ULift.{u} (Fin 1)) (base k) := rfl

/-- The involution commutes with the structure morphism of the affine line. -/
theorem involution_comp_hom (k : Type u) [Field k] :
    (involution k).left ≫ (cover k).hom = (cover k).hom := by
  exact AffineSpace.homOfVector_over _ _

/-- The unique coordinate function on the affine line over `k`. -/
def coord (k : Type u) [Field k] : Γ((cover k).left, ⊤) :=
  AffineSpace.coord (base k) (ULift.up (0 : Fin 1))

/-- `coord k` is the standard coordinate of `𝔸¹_k`. -/
theorem coord_eq (k : Type u) [Field k] :
    coord k = AffineSpace.coord (base k) (ULift.up (0 : Fin 1)) := rfl

/-- The basic open `D(x) ⊆ 𝔸¹_k` on which the coordinate is invertible. -/
def puncturedOpen (k : Type u) [Field k] : (cover k).left.Opens :=
  (cover k).left.basicOpen (coord k)

/-- The punctured open is the basic open of the unique coordinate. -/
theorem puncturedOpen_eq (k : Type u) [Field k] :
    puncturedOpen k = (cover k).left.basicOpen (coord k) := rfl

/-- A point of the affine line lies in `D(x)` exactly when it lies in the basic open of the
coordinate. -/
theorem mem_puncturedOpen_iff (k : Type u) [Field k] (x : (cover k).left) :
    x ∈ puncturedOpen k ↔ x ∈ (cover k).left.basicOpen (coord k) := Iff.rfl

/-- The open `D(x)` as a scheme over `Spec k`. -/
def puncturedOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk ((puncturedOpen k).ι ≫ (cover k).hom)

/-- The structure morphism of `puncturedOver` is the composite of the open immersion with the
structure map of the affine line. -/
theorem puncturedOver_hom (k : Type u) [Field k] :
    (puncturedOver k).hom = (puncturedOpen k).ι ≫ (cover k).hom := rfl

/-- The open immersion `D(x) ⟶ 𝔸¹_k` as a morphism over `Spec k`. -/
def puncturedι (k : Type u) [Field k] : puncturedOver k ⟶ cover k :=
  Over.homMk (puncturedOpen k).ι

/-- The underlying scheme map of `puncturedι` is the open immersion of `D(x)`. -/
theorem puncturedι_left (k : Type u) [Field k] :
    (puncturedι k).left = (puncturedOpen k).ι := rfl

/-- The inclusion of `D(x)` into the affine line is an open immersion. -/
instance instIsOpenImmersion_puncturedι (k : Type u) [Field k] :
    IsOpenImmersion (puncturedι k).left := by
  change IsOpenImmersion (puncturedOpen k).ι
  infer_instance

/-- The relative diagonal `Δ ⟶ U ×_k U` of the affine line. -/
def diagonalHom (k : Type u) [Field k] : cover k ⟶ cover k ⨯ cover k :=
  prod.lift (𝟙 (cover k)) (𝟙 (cover k))

/-- The diagonal summand map is the relative diagonal of `U` over `Spec k`. -/
theorem diagonalHom_eq (k : Type u) [Field k] :
    diagonalHom k = prod.lift (𝟙 (cover k)) (𝟙 (cover k)) := rfl

/-- The graph of `x ↦ -x` on `D(x)`, as a morphism `Γ ⟶ U ×_k U`. -/
def graphHom (k : Type u) [Field k] : puncturedOver k ⟶ cover k ⨯ cover k :=
  puncturedι k ≫ prod.lift (𝟙 (cover k)) (involution k)

/-- The first projection of the graph summand is the open immersion `D(x) ⟶ U`. -/
theorem graphHom_fst (k : Type u) [Field k] :
    graphHom k ≫ prod.fst = puncturedι k := by
  rw [graphHom, Category.assoc, prod.lift_fst, Category.comp_id]

/-- The second projection of the graph summand is the composite of the open immersion with
coordinatewise negation. -/
theorem graphHom_snd (k : Type u) [Field k] :
    graphHom k ≫ prod.snd = puncturedι k ≫ involution k := by
  rw [graphHom, Category.assoc, prod.lift_snd]

/-- The `i`-th summand of the relation scheme: the affine line on the diagonal index, and
`D(x)` on the graph index. -/
def relationComponent (k : Type u) [Field k] : relationIndex → Over (base k)
  | false => cover k
  | true => puncturedOver k

/-- The diagonal summand of the relation is the cover `U`. -/
theorem relationComponent_false (k : Type u) [Field k] :
    relationComponent k false = cover k := rfl

/-- The graph summand of the relation is the punctured affine line `D(x)`. -/
theorem relationComponent_true (k : Type u) [Field k] :
    relationComponent k true = puncturedOver k := rfl

/-- The component of `j` on the summand indexed by `i`: the relative diagonal on `U`, and the
graph of negation on `D(x)`. -/
def relationComponentHom (k : Type u) [Field k] :
    (i : relationIndex) → relationComponent k i ⟶ cover k ⨯ cover k
  | false => diagonalHom k
  | true => graphHom k

/-- On the diagonal summand, `j` is the relative diagonal of `U` over `Spec k`. -/
theorem relationComponentHom_false (k : Type u) [Field k] :
    relationComponentHom k false = diagonalHom k := rfl

/-- On the graph summand, `j` is the graph of `x ↦ -x` on `D(x)`. -/
theorem relationComponentHom_true (k : Type u) [Field k] :
    relationComponentHom k true = graphHom k := rfl

/-- The relation scheme `R = Δ ⨿ Γ` as an object over `Spec k`. -/
def relationOver (k : Type u) [Field k] : Over (base k) :=
  ∐ relationComponent k

/-- The underlying object of `relationOver` is the coproduct of the relation summands. -/
theorem relationOver_eq (k : Type u) [Field k] :
    relationOver k = ∐ relationComponent k := rfl

/-- The morphism `j : R ⟶ U ×_k U` equal to the relative diagonal on `Δ` and to the graph of
negation on `Γ`. -/
def relationHom (k : Type u) [Field k] : relationOver k ⟶ cover k ⨯ cover k :=
  Sigma.desc (relationComponentHom k)

/-- The defining map of the relation is the coproduct fold of the component maps. -/
theorem relationHom_eq (k : Type u) [Field k] :
    relationHom k = Sigma.desc (relationComponentHom k) := rfl

/-- The pre-relation on `U` over `Spec k` with source `R` and defining map `j`. -/
def preRelation (k : Type u) [Field k] : Scheme.PreRelation (cover k) :=
  Scheme.PreRelation.ofHom (relationHom k)

/-- The defining arrow of `preRelation k` is `relationHom k`. -/
theorem preRelation_hom (k : Type u) [Field k] :
    (preRelation k).hom = relationHom k := rfl

/-- The first projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_t_false (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) false ≫ (preRelation k).t = 𝟙 (cover k) := by
  change Sigma.ι (relationComponent k) false ≫
    (Sigma.desc (relationComponentHom k) ≫ prod.fst) = _
  rw [← Category.assoc, Sigma.ι_desc]
  exact prod.lift_fst _ _

/-- The second projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_s_false (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) false ≫ (preRelation k).s = 𝟙 (cover k) := by
  change Sigma.ι (relationComponent k) false ≫
    (Sigma.desc (relationComponentHom k) ≫ prod.snd) = _
  rw [← Category.assoc, Sigma.ι_desc]
  exact prod.lift_snd _ _

/-- The first projection of the relation, restricted to the graph summand, is the open
immersion `D(x) ⟶ U`. -/
theorem preRelation_t_true (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) true ≫ (preRelation k).t = puncturedι k := by
  change Sigma.ι (relationComponent k) true ≫
    (Sigma.desc (relationComponentHom k) ≫ prod.fst) = _
  rw [← Category.assoc, Sigma.ι_desc]
  exact graphHom_fst k

/-- The second projection of the relation, restricted to the graph summand, is the graph of
`x ↦ -x`. -/
theorem preRelation_s_true (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) true ≫ (preRelation k).s =
      puncturedι k ≫ involution k := by
  change Sigma.ι (relationComponent k) true ≫
    (Sigma.desc (relationComponentHom k) ≫ prod.snd) = _
  rw [← Category.assoc, Sigma.ι_desc]
  exact graphHom_snd k

/-- The two projections of `j` are étale and `j` is an equivalence relation. -/
instance instIsEtaleEquivalenceRelation_preRelation (k : Type u) [Field k] [NeZero (2 : k)] :
    (preRelation k).IsEtaleEquivalenceRelation := sorry

/-- The relation scheme `R = Δ ⨿ Γ` is quasi-compact. -/
instance instCompactSpace_relationOver (k : Type u) [Field k] :
    CompactSpace (relationOver k).left := by
  haveI : IsAffine (cover k).left := by
    change IsAffine 𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of k))
    infer_instance
  haveI : IsAffine (puncturedOver k).left := by
    change IsAffine ((cover k).left.basicOpen (coord k))
    infer_instance
  haveI : ∀ i : relationIndex, IsAffine (relationComponent k i).left := by
    intro i
    cases i <;> assumption
  haveI : IsAffine (∐ fun i : relationIndex ↦ (relationComponent k i).left) :=
    inferInstance
  haveI : IsAffine (relationOver k).left := by
    refine @IsAffine.of_isIso _ _
      (PreservesCoproduct.iso (Over.forget (base k)) (relationComponent k)).hom
      (by infer_instance) ?_
    change IsAffine (∐ fun i : relationIndex ↦ (relationComponent k i).left)
    infer_instance
  infer_instance

/-- The morphism `j : R ⟶ U ×_k U` is not an immersion. -/
theorem not_isImmersion_relationHom (k : Type u) [Field k] [NeZero (2 : k)] :
    ¬ IsImmersion (relationHom k).left := sorry


/-- The fppf sheaf `X = U / R`, obtained by sheafifying the universe-raised quotient presheaf. -/
def sheafOfPoints (k : Type u) [Field k] :
    Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)) :=
  (preRelation k).quotientSheaf (Scheme.fppfTopology.over (base k))

/-- `sheafOfPoints k` is the fppf quotient sheaf of the affine-line involution pre-relation. -/
theorem sheafOfPoints_eq (k : Type u) [Field k] :
    sheafOfPoints k = (preRelation k).quotientSheaf (Scheme.fppfTopology.over (base k)) := rfl

/-- The atlas `U ⟶ X` as a morphism of fppf sheaves, given by the canonical quotient map. -/
def atlas (k : Type u) [Field k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) ⟶ sheafOfPoints k :=
  (preRelation k).quotientMap (Scheme.fppfTopology.over (base k))

/-- The atlas is the canonical fppf quotient map of the pre-relation. -/
theorem atlas_eq (k : Type u) [Field k] :
    atlas k = (preRelation k).quotientMap (Scheme.fppfTopology.over (base k)) := rfl

/-- The fppf quotient sheaf `X = U / R` is an algebraic space over `Spec k`: it has a
representable étale locally-surjective atlas from `U` and a representable diagonal. -/
theorem sheafOfPoints_spec (k : Type u) [Field k] [NeZero (2 : k)] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom ∧
        uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj) := by
  have h := (preRelation k).quotientSheaf_spec
  exact ⟨h.2.1, h.2.2, h.1⟩

/-- The diagonal of `X = U / R` is quasi-compact relative to `uliftYoneda`, so `X` is
quasi-separated. -/
theorem quasiCompact_diag_sheafOfPoints (k : Type u) [Field k] [NeZero (2 : k)] :
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag (sheafOfPoints k).obj) := sorry

/-- The diagonal of `X = U / R` is not an immersion relative to `uliftYoneda`, so `X` is not
locally separated. -/
theorem not_isImmersion_diag_sheafOfPoints (k : Type u) [Field k] [NeZero (2 : k)] :
    ¬ (MorphismProperty.over (@IsImmersion)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) := sorry


end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
