/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# Coordinate-axes étale equivalence relation

This module records the union of coordinate axes `U = Spec(k[x, y] / (xy))` in `𝔸²_k`
and the étale equivalence relation `R = Δ(U) ⨿ Δ'(U \ {0_U})` whose second summand is
the graph of the axis-flipping automorphism `σ : (x, y) ↦ (y, x)` on `D(x + y)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open MvPolynomial
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient

/-- The base scheme `Spec k`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of.{u} k)


/-- The relation polynomial `xy` in `k[x, y]`. -/
def relationPoly (k : Type u) [Field k] : MvPolynomial (ULift.{u} (Fin 2)) k :=
  X (ULift.up (0 : Fin 2)) * X (ULift.up (1 : Fin 2))


/-- The principal ideal `(xy)` in `k[x, y]`. -/
def relationIdeal (k : Type u) [Field k] : Ideal (MvPolynomial (ULift.{u} (Fin 2)) k) :=
  Ideal.span {relationPoly k}


/-- The generator `xy` lies in the relation ideal. -/
private theorem mem_span_relationPoly (k : Type u) [Field k] :
    relationPoly k ∈ relationIdeal k := sorry

/-- The coordinate ring `k[x, y] / (xy)` of the union of the coordinate axes. -/
def coordinateRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (ULift.{u} (Fin 2)) k ⧸ relationIdeal k


/-- The coordinate ring is a commutative ring. -/
instance instCommRing_coordinateRing (k : Type u) [Field k] : CommRing (coordinateRing k) :=
  inferInstanceAs (CommRing (MvPolynomial (ULift.{u} (Fin 2)) k ⧸ relationIdeal k))

/-- The coordinate ring is a `k`-algebra. -/
instance instAlgebra_coordinateRing (k : Type u) [Field k] : Algebra k (coordinateRing k) :=
  inferInstanceAs (Algebra k (MvPolynomial (ULift.{u} (Fin 2)) k ⧸ relationIdeal k))

/-- The union of the coordinate axes `U = Spec(k[x, y] / (xy))` as a scheme over `Spec k`. -/
def cover (k : Type u) [Field k] : Over (base k) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing k))))

/-- The underlying scheme of the cover is the spectrum of the coordinate ring. -/
theorem cover_left (k : Type u) [Field k] :
    (cover k).left = Spec (CommRingCat.of (coordinateRing k)) := rfl

/-- The structure morphism of the cover is `Spec` of the algebra map `k → k[x, y] / (xy)`. -/
theorem cover_hom (k : Type u) [Field k] :
    (cover k).hom = Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing k))) := rfl

/-- The closed immersion of the coordinate axes into `𝔸²_k`. -/
def toAffinePlane (k : Type u) [Field k] : (cover k).left ⟶ 𝔸(ULift.{u} (Fin 2); base k) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (relationIdeal k))) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).inv

/-- The closed immersion into the affine plane composes with the structure morphism of
`𝔸²_k` to the structure morphism of `U`. -/
theorem toAffinePlane_comp_hom (k : Type u) [Field k] :
    toAffinePlane k ≫ (𝔸(ULift.{u} (Fin 2); base k) ↘ base k) = (cover k).hom := sorry

/-- The morphism `U ⟶ 𝔸²_k` is a closed immersion. -/
instance instIsClosedImmersion_toAffinePlane (k : Type u) [Field k] :
    IsClosedImmersion (toAffinePlane k) := sorry

/-- The class of the `i`-th coordinate in the global sections of `U`. -/
def coord (k : Type u) [Field k] (i : ULift.{u} (Fin 2)) : Γ((cover k).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing k))).inv
    (Ideal.Quotient.mk (relationIdeal k) (X i))


/-- The global section `x + y` on `U`. -/
def sumSection (k : Type u) [Field k] : Γ((cover k).left, ⊤) :=
  coord k (ULift.up (0 : Fin 2)) + coord k (ULift.up (1 : Fin 2))


/-- The automorphism of `k[x, y]` swapping the two variables. -/
def flipRename (k : Type u) [Field k] :
    MvPolynomial (ULift.{u} (Fin 2)) k ≃ₐ[k] MvPolynomial (ULift.{u} (Fin 2)) k :=
  MvPolynomial.renameEquiv k
    (Equiv.swap (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)))


/-- Renaming by the coordinate swap sends the relation ideal into itself. -/
private theorem flipRename_eq_zero_of_mem (k : Type u) [Field k]
    (a : MvPolynomial (ULift.{u} (Fin 2)) k) (ha : a ∈ relationIdeal k) :
    Ideal.Quotient.mk (relationIdeal k) (flipRename k a) = 0 := sorry

/-- The induced automorphism of `k[x, y] / (xy)` swapping the two coordinates. -/
def flipRingHom (k : Type u) [Field k] : coordinateRing k →+* coordinateRing k :=
  Ideal.Quotient.lift (relationIdeal k)
    ((Ideal.Quotient.mk (relationIdeal k)).comp (flipRename k).toRingHom)
    (by exact flipRename_eq_zero_of_mem k)


/-- The axis-flipping automorphism of `U` commutes with the structure morphism to `Spec k`. -/
private theorem flip_w (k : Type u) [Field k] :
    Spec.map (CommRingCat.ofHom (flipRingHom k)) ≫ (cover k).hom = (cover k).hom := sorry

/-- The automorphism `σ : U ⟶ U` flipping the coordinate axes, `(x, y) ↦ (y, x)`. -/
def flip (k : Type u) [Field k] : cover k ⟶ cover k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (flipRingHom k))) (by exact flip_w k)

/-- The underlying scheme map of `flip` is `Spec` of the coordinate-swapping automorphism. -/
theorem flip_left (k : Type u) [Field k] :
    (flip k).left = Spec.map (CommRingCat.ofHom (flipRingHom k)) := rfl

/-- Flipping the axes is an isomorphism of `U` over `Spec k`. -/
instance instIsIso_flip (k : Type u) [Field k] : IsIso (flip k) := sorry

/-- The axis-flipping automorphism is an involution. -/
theorem flip_comp_flip (k : Type u) [Field k] : flip k ≫ flip k = 𝟙 (cover k) := sorry

/-- On global sections, `flip` swaps the two coordinates. -/
theorem flip_appTop_coord (k : Type u) [Field k] (i : ULift.{u} (Fin 2)) :
    (flip k).left.appTop (coord k i) =
      coord k (Equiv.swap (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)) i) := sorry

/-- Evaluation of polynomials at the origin `(0, 0)`. -/
def originEvalPoly (k : Type u) [Field k] : MvPolynomial (ULift.{u} (Fin 2)) k →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun _ ↦ 0)

/-- The origin evaluation kills the relation ideal. -/
private theorem originEvalPoly_eq_zero_of_mem (k : Type u) [Field k]
    (a : MvPolynomial (ULift.{u} (Fin 2)) k) (ha : a ∈ relationIdeal k) :
    originEvalPoly k a = 0 := sorry

/-- The unique `k`-algebra map `k[x, y] / (xy) → k` sending both coordinates to `0`. -/
def originEval (k : Type u) [Field k] : coordinateRing k →+* k :=
  Ideal.Quotient.lift (relationIdeal k) (originEvalPoly k) (by exact originEvalPoly_eq_zero_of_mem k)


/-- The underlying scheme morphism of the origin of `U`. -/
def originToCoverLeft (k : Type u) [Field k] : base k ⟶ (cover k).left :=
  Spec.map (CommRingCat.ofHom (originEval k))


/-- The origin `Spec k` of `U`, viewed as a scheme over `Spec k`. -/
def originOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk (originToCoverLeft k ≫ (cover k).hom)


/-- The origin morphism `Spec k ⟶ U` over `Spec k`. -/
def originToCover (k : Type u) [Field k] : originOver k ⟶ cover k :=
  Over.homMk (originToCoverLeft k)

/-- The origin of `U` is irreducible, as it is `Spec k`. -/
instance instIrreducibleSpace_originOver (k : Type u) [Field k] :
    IrreducibleSpace (originOver k).left := inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of k)))

/-- The underlying scheme morphism of `originToCover` is evaluation at the origin. -/
theorem originToCover_left (k : Type u) [Field k] :
    (originToCover k).left = originToCoverLeft k := rfl

/-- The origin point `0_U ∈ U`. -/
def originPoint (k : Type u) [Field k] : (cover k).left :=
  (originToCover k).left.base (genericPoint (originOver k).left)


/-- The basic open `D(x + y) ⊆ U`, which is `U \ {0_U}`. -/
def puncturedOpen (k : Type u) [Field k] : (cover k).left.Opens :=
  (cover k).left.basicOpen (sumSection k)


/-- A point of `U` lies in `D(x + y)` exactly when it is not the origin. -/
theorem mem_puncturedOpen_iff_ne_origin (k : Type u) [Field k] (x : (cover k).left) :
    x ∈ puncturedOpen k ↔ x ≠ originPoint k := sorry

/-- The open `U \ {0_U}` as a scheme over `Spec k`. -/
def puncturedOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk ((puncturedOpen k).ι ≫ (cover k).hom)

/-- The structure morphism of `puncturedOver` is the composite of the open immersion with the
structure map of `U`. -/
theorem puncturedOver_hom (k : Type u) [Field k] :
    (puncturedOver k).hom = (puncturedOpen k).ι ≫ (cover k).hom := rfl

/-- The open immersion `U \ {0_U} ⟶ U` as a morphism over `Spec k`. -/
def puncturedι (k : Type u) [Field k] : puncturedOver k ⟶ cover k :=
  Over.homMk (puncturedOpen k).ι

/-- The underlying scheme map of `puncturedι` is the open immersion of `D(x + y)`. -/
theorem puncturedι_left (k : Type u) [Field k] :
    (puncturedι k).left = (puncturedOpen k).ι := rfl

/-- The inclusion of `U \ {0_U}` into `U` is an open immersion. -/
instance instIsOpenImmersion_puncturedι (k : Type u) [Field k] :
    IsOpenImmersion (puncturedι k).left := inferInstanceAs (IsOpenImmersion (puncturedOpen k).ι)

/-- The relative diagonal `Δ ⟶ U ×_k U`. -/
def diagonalHom (k : Type u) [Field k] : cover k ⟶ cover k ⨯ cover k :=
  prod.lift (𝟙 (cover k)) (𝟙 (cover k))


/-- The graph of `σ` on `U \ {0_U}`, as a morphism `Δ' ⟶ U ×_k U`. -/
def graphHom (k : Type u) [Field k] : puncturedOver k ⟶ cover k ⨯ cover k :=
  puncturedι k ≫ prod.lift (𝟙 (cover k)) (flip k)

/-- The first projection of the graph summand is the open immersion `U \ {0_U} ⟶ U`. -/
theorem graphHom_fst (k : Type u) [Field k] :
    graphHom k ≫ prod.fst = puncturedι k := sorry

/-- The second projection of the graph summand is the composite of the open immersion with
axis-flipping. -/
theorem graphHom_snd (k : Type u) [Field k] :
    graphHom k ≫ prod.snd = puncturedι k ≫ flip k := sorry

/-- The `i`-th summand of the relation scheme: `U` on the diagonal index, and `U \ {0_U}`
on the graph index. -/
def relationComponent (k : Type u) [Field k] : Bool → Over (base k)
  | false => cover k
  | true => puncturedOver k

/-- The diagonal summand of the relation is the cover `U`. -/
theorem relationComponent_false (k : Type u) [Field k] :
    relationComponent k false = cover k := rfl

/-- The graph summand of the relation is the punctured cover `U \ {0_U}`. -/
theorem relationComponent_true (k : Type u) [Field k] :
    relationComponent k true = puncturedOver k := rfl

/-- The component of `j` on the summand indexed by `i`: the relative diagonal on `U`, and the
graph of axis-flipping on `U \ {0_U}`. -/
def relationComponentHom (k : Type u) [Field k] :
    (i : Bool) → relationComponent k i ⟶ cover k ⨯ cover k
  | false => diagonalHom k
  | true => graphHom k

/-- On the diagonal summand, `j` is the relative diagonal of `U` over `Spec k`. -/
theorem relationComponentHom_false (k : Type u) [Field k] :
    relationComponentHom k false = diagonalHom k := rfl

/-- On the graph summand, `j` is the graph of `σ` on `U \ {0_U}`. -/
theorem relationComponentHom_true (k : Type u) [Field k] :
    relationComponentHom k true = graphHom k := rfl

/-- The relation scheme `R = Δ ⨿ Δ'` as an object over `Spec k`. -/
def relationOver (k : Type u) [Field k] : Over (base k) :=
  ∐ relationComponent k


/-- The morphism `j : R ⟶ U ×_k U` equal to the relative diagonal on `Δ` and to the graph of
axis-flipping on `Δ'`. -/
def relationHom (k : Type u) [Field k] : relationOver k ⟶ cover k ⨯ cover k :=
  Sigma.desc (relationComponentHom k)


/-- The pre-relation on `U` over `Spec k` with source `R` and defining map `j`. -/
def preRelation (k : Type u) [Field k] : Scheme.PreRelation (cover k) :=
  Scheme.PreRelation.ofHom (relationHom k)

/-- The defining arrow of `preRelation k` is `relationHom k`. -/
theorem preRelation_hom (k : Type u) [Field k] :
    (preRelation k).hom = relationHom k := rfl

/-- The first projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_t_false (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) false ≫ (preRelation k).t = 𝟙 (cover k) := sorry

/-- The second projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_s_false (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) false ≫ (preRelation k).s = 𝟙 (cover k) := sorry

/-- The first projection of the relation, restricted to the graph summand, is the open
immersion `U \ {0_U} ⟶ U`. -/
theorem preRelation_t_true (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) true ≫ (preRelation k).t = puncturedι k := sorry

/-- The second projection of the relation, restricted to the graph summand, is the graph of
axis-flipping. -/
theorem preRelation_s_true (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) true ≫ (preRelation k).s =
      puncturedι k ≫ flip k := sorry

/-- The two projections of `j` are étale and `j` is an equivalence relation. -/
instance instIsEtaleEquivalenceRelation_preRelation (k : Type u) [Field k] :
    (preRelation k).IsEtaleEquivalenceRelation := sorry

/-- The relation scheme `R = Δ ⨿ Δ'` is quasi-compact. -/
instance instCompactSpace_relationOver (k : Type u) [Field k] :
    CompactSpace (relationOver k).left := sorry

end AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient
