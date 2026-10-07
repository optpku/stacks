module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import ReasLib.AlgebraicGeometry.AffineSpace.AdditiveGroup
public import ReasLib.AlgebraicGeometry.Scheme.Variety.AffinePresentation
public import stacks_project.Chap65.Definition_65_9_3_EtaleEquivalence

/-!
# Affine-line involution étale equivalence relation

This module records the affine line `𝔸¹_k` over `Spec k` and the étale equivalence relation
`j : Δ ⨿ Γ ⟶ U ×_k U` whose diagonal summand is the relative diagonal and whose second
summand is the graph of `x ↦ -x` on `D(x)`.
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
theorem relationIndex_eq : relationIndex = Bool := sorry

/-- The relation index is `u`-small, so the coproduct of relation summands exists in `Scheme`. -/
instance instSmallRelationIndex : Small.{u} relationIndex := inferInstance

/-- The base scheme `Spec k`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of.{u} k)

/-- The base scheme is the spectrum of `k`. -/
theorem base_eq (k : Type u) [Field k] : base k = Spec (CommRingCat.of.{u} k) := sorry

/-- The affine line `U = 𝔸¹_k` as a scheme over `Spec k`. -/
def cover (k : Type u) [Field k] : Over (base k) :=
  Over.mk (affineSpaceOverFieldHom k 1)

/-- The underlying scheme of the cover is affine 1-space over `k`. -/
theorem cover_left (k : Type u) [Field k] :
    (cover k).left = AffineSpaceOverField k 1 := sorry

/-- The structure morphism of the cover is the canonical map `𝔸¹_k ⟶ Spec k`. -/
theorem cover_hom (k : Type u) [Field k] :
    (cover k).hom = affineSpaceOverFieldHom k 1 := sorry

/-- Coordinatewise negation `x ↦ -x` on the affine line, as a morphism over `Spec k`. -/
def involution (k : Type u) [Field k] : cover k ⟶ cover k :=
  Over.homMk (AffineSpace.negLeft (ULift.{u} (Fin 1)) (base k))
    (AffineSpace.negHom_w (ULift.{u} (Fin 1)) (base k))

/-- The underlying scheme map of the involution is coordinatewise negation. -/
theorem involution_left (k : Type u) [Field k] :
    (involution k).left = AffineSpace.negLeft (ULift.{u} (Fin 1)) (base k) := sorry

/-- The involution commutes with the structure morphism of the affine line. -/
theorem involution_comp_hom (k : Type u) [Field k] :
    (involution k).left ≫ (cover k).hom = (cover k).hom := sorry

/-- The unique coordinate function on the affine line over `k`. -/
def coord (k : Type u) [Field k] : Γ((cover k).left, ⊤) :=
  AffineSpace.coord (base k) (ULift.up (0 : Fin 1))

/-- `coord k` is the standard coordinate of `𝔸¹_k`. -/
theorem coord_eq (k : Type u) [Field k] :
    coord k = AffineSpace.coord (base k) (ULift.up (0 : Fin 1)) := sorry

/-- The basic open `D(x) ⊆ 𝔸¹_k` on which the coordinate is invertible. -/
def puncturedOpen (k : Type u) [Field k] : (cover k).left.Opens :=
  (cover k).left.basicOpen (coord k)

/-- The punctured open is the basic open of the unique coordinate. -/
theorem puncturedOpen_eq (k : Type u) [Field k] :
    puncturedOpen k = (cover k).left.basicOpen (coord k) := sorry

/-- A point of the affine line lies in `D(x)` exactly when it lies in the basic open of the
coordinate. -/
theorem mem_puncturedOpen_iff (k : Type u) [Field k] (x : (cover k).left) :
    x ∈ puncturedOpen k ↔ x ∈ (cover k).left.basicOpen (coord k) := sorry

/-- The open `D(x)` as a scheme over `Spec k`. -/
def puncturedOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk ((puncturedOpen k).ι ≫ (cover k).hom)

/-- The structure morphism of `puncturedOver` is the composite of the open immersion with the
structure map of the affine line. -/
theorem puncturedOver_hom (k : Type u) [Field k] :
    (puncturedOver k).hom = (puncturedOpen k).ι ≫ (cover k).hom := sorry

/-- The open immersion `D(x) ⟶ 𝔸¹_k` as a morphism over `Spec k`. -/
def puncturedι (k : Type u) [Field k] : puncturedOver k ⟶ cover k :=
  Over.homMk (puncturedOpen k).ι

/-- The underlying scheme map of `puncturedι` is the open immersion of `D(x)`. -/
theorem puncturedι_left (k : Type u) [Field k] :
    (puncturedι k).left = (puncturedOpen k).ι := sorry

/-- The inclusion of `D(x)` into the affine line is an open immersion. -/
instance instIsOpenImmersion_puncturedι (k : Type u) [Field k] :
    IsOpenImmersion (puncturedι k).left := sorry

/-- The relative diagonal `Δ ⟶ U ×_k U` of the affine line. -/
def diagonalHom (k : Type u) [Field k] : cover k ⟶ cover k ⨯ cover k :=
  prod.lift (𝟙 (cover k)) (𝟙 (cover k))

/-- The diagonal summand map is the relative diagonal of `U` over `Spec k`. -/
theorem diagonalHom_eq (k : Type u) [Field k] :
    diagonalHom k = prod.lift (𝟙 (cover k)) (𝟙 (cover k)) := sorry

/-- The graph of `x ↦ -x` on `D(x)`, as a morphism `Γ ⟶ U ×_k U`. -/
def graphHom (k : Type u) [Field k] : puncturedOver k ⟶ cover k ⨯ cover k :=
  puncturedι k ≫ prod.lift (𝟙 (cover k)) (involution k)

/-- The first projection of the graph summand is the open immersion `D(x) ⟶ U`. -/
theorem graphHom_fst (k : Type u) [Field k] :
    graphHom k ≫ prod.fst = puncturedι k := sorry

/-- The second projection of the graph summand is the composite of the open immersion with
coordinatewise negation. -/
theorem graphHom_snd (k : Type u) [Field k] :
    graphHom k ≫ prod.snd = puncturedι k ≫ involution k := sorry

/-- The `i`-th summand of the relation scheme: the affine line on the diagonal index, and
`D(x)` on the graph index. -/
def relationComponent (k : Type u) [Field k] : relationIndex → Over (base k)
  | false => cover k
  | true => puncturedOver k

/-- The diagonal summand of the relation is the cover `U`. -/
theorem relationComponent_false (k : Type u) [Field k] :
    relationComponent k false = cover k := sorry

/-- The graph summand of the relation is the punctured affine line `D(x)`. -/
theorem relationComponent_true (k : Type u) [Field k] :
    relationComponent k true = puncturedOver k := sorry

/-- The component of `j` on the summand indexed by `i`: the relative diagonal on `U`, and the
graph of negation on `D(x)`. -/
def relationComponentHom (k : Type u) [Field k] :
    (i : relationIndex) → relationComponent k i ⟶ cover k ⨯ cover k
  | false => diagonalHom k
  | true => graphHom k

/-- On the diagonal summand, `j` is the relative diagonal of `U` over `Spec k`. -/
theorem relationComponentHom_false (k : Type u) [Field k] :
    relationComponentHom k false = diagonalHom k := sorry

/-- On the graph summand, `j` is the graph of `x ↦ -x` on `D(x)`. -/
theorem relationComponentHom_true (k : Type u) [Field k] :
    relationComponentHom k true = graphHom k := sorry

/-- The relation scheme `R = Δ ⨿ Γ` as an object over `Spec k`. -/
def relationOver (k : Type u) [Field k] : Over (base k) :=
  ∐ relationComponent k

/-- The underlying object of `relationOver` is the coproduct of the relation summands. -/
theorem relationOver_eq (k : Type u) [Field k] :
    relationOver k = ∐ relationComponent k := sorry

/-- The morphism `j : R ⟶ U ×_k U` equal to the relative diagonal on `Δ` and to the graph of
negation on `Γ`. -/
def relationHom (k : Type u) [Field k] : relationOver k ⟶ cover k ⨯ cover k :=
  Sigma.desc (relationComponentHom k)

/-- The defining map of the relation is the coproduct fold of the component maps. -/
theorem relationHom_eq (k : Type u) [Field k] :
    relationHom k = Sigma.desc (relationComponentHom k) := sorry

/-- The pre-relation on `U` over `Spec k` with source `R` and defining map `j`. -/
def preRelation (k : Type u) [Field k] : Scheme.PreRelation (cover k) :=
  Scheme.PreRelation.ofHom (relationHom k)

/-- The defining arrow of `preRelation k` is `relationHom k`. -/
theorem preRelation_hom (k : Type u) [Field k] :
    (preRelation k).hom = relationHom k := sorry

/-- The first projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_t_false (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) false ≫ (preRelation k).t = 𝟙 (cover k) := sorry

/-- The second projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_s_false (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) false ≫ (preRelation k).s = 𝟙 (cover k) := sorry

/-- The first projection of the relation, restricted to the graph summand, is the open
immersion `D(x) ⟶ U`. -/
theorem preRelation_t_true (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) true ≫ (preRelation k).t = puncturedι k := sorry

/-- The second projection of the relation, restricted to the graph summand, is the graph of
`x ↦ -x`. -/
theorem preRelation_s_true (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) true ≫ (preRelation k).s =
      puncturedι k ≫ involution k := sorry

/-- The two projections of `j` are étale and `j` is an equivalence relation. -/
instance instIsEtaleEquivalenceRelation_preRelation (k : Type u) [Field k] [NeZero (2 : k)] :
    (preRelation k).IsEtaleEquivalenceRelation := sorry

/-- The relation scheme `R = Δ ⨿ Γ` is quasi-compact. -/
instance instCompactSpace_relationOver (k : Type u) [Field k] :
    CompactSpace (relationOver k).left := sorry

/-- The morphism `j : R ⟶ U ×_k U` is not an immersion. -/
theorem not_isImmersion_relationHom (k : Type u) [Field k] [NeZero (2 : k)] :
    ¬ IsImmersion (relationHom k).left := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
