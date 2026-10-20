/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.RingTheory.Ideal.Span
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# Infinite product étale equivalence relation

This module records the affine cover `Spec(ℕ → k)` over `Spec k` and the étale equivalence
relation obtained by attaching off-diagonal copies of `Spec k` to the relative diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InfiniteProduct

/-- The infinite product ring `ℕ → k`. -/
abbrev productRing (k : Type u) [Field k] : Type u := ℕ → k

/-- The underlying ring of `productRing k` is the pointwise product. -/
theorem productRing_eq (k : Type u) [Field k] : productRing k = (ℕ → k) := sorry

/-- The pairs of distinct natural numbers indexing off-diagonal copies of `S`. -/
abbrev offDiagonal : Type := { p : ℕ × ℕ // p.1 ≠ p.2 }

/-- Membership in `offDiagonal` is inequality of the two coordinates. -/
theorem mem_offDiagonal_iff (p : ℕ × ℕ) : p ∈ { q : ℕ × ℕ | q.1 ≠ q.2 } ↔ p.1 ≠ p.2 := sorry

/-- The index type of the relation scheme: the diagonal summand together with an
off-diagonal copy of `S` for each `n ≠ m`. -/
abbrev relationIndex : Type := Option offDiagonal

/-- The relation index is the option type on off-diagonal pairs. -/
theorem relationIndex_eq : relationIndex = Option offDiagonal := sorry

/-- The relation index is `u`-small, so the coproduct of relation summands exists in `Scheme`. -/
instance instSmallRelationIndex : Small.{u} relationIndex := inferInstance

/-- The base scheme `S = Spec(k)`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of k)

/-- The base scheme is the spectrum of `k`. -/
theorem base_eq (k : Type u) [Field k] : base k = Spec (CommRingCat.of k) := sorry

/-- The structure morphism of the infinite product, induced by the constant algebra map. -/
def productAlgebraMap (k : Type u) [Field k] :
    CommRingCat.of k ⟶ CommRingCat.of (productRing k) :=
  CommRingCat.ofHom (algebraMap k (productRing k))

/-- The structure map is the constant algebra map `k → ℕ → k`. -/
theorem productAlgebraMap_eq (k : Type u) [Field k] :
    productAlgebraMap k = CommRingCat.ofHom (algebraMap k (ℕ → k)) := sorry

/-- The scheme `U = Spec(ℕ → k)` over `S = Spec(k)`. -/
def cover (k : Type u) [Field k] : Over (base k) :=
  OverSpec.affine (productAlgebraMap k)

/-- The underlying scheme of the cover is `Spec(ℕ → k)`. -/
theorem cover_left (k : Type u) [Field k] :
    (cover k).left = Spec (CommRingCat.of (ℕ → k)) := sorry

/-- The structure morphism of the cover is `Spec` of the constant algebra map. -/
theorem cover_hom (k : Type u) [Field k] :
    (cover k).hom = Spec.map (productAlgebraMap k) := sorry

/-- The open-and-closed immersion `f_n : S ⟶ U` induced by the projection `pr_n : A → k`. -/
def immersion (k : Type u) [Field k] (n : ℕ) : base k ⟶ (cover k).left :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ℕ ↦ k) n))

/-- The immersion `f_n` is `Spec` of the product projection at `n`. -/
theorem immersion_def (k : Type u) [Field k] (n : ℕ) :
    immersion k n =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ℕ ↦ k) n)) := sorry

/-- The projection `pr_n` is compatible with the structure map of `U` over `S`. -/
theorem immersion_comp_cover_hom (k : Type u) [Field k] (n : ℕ) :
    immersion k n ≫ (cover k).hom = 𝟙 (base k) := sorry

/-- Each projection `pr_n` defines an open immersion `f_n : S ⟶ U`. -/
instance instIsOpenImmersion_immersion (k : Type u) [Field k] (n : ℕ) :
    IsOpenImmersion (immersion k n) := sorry

/-- Each projection `pr_n` defines a closed immersion `f_n : S ⟶ U`. -/
instance instIsClosedImmersion_immersion (k : Type u) [Field k] (n : ℕ) :
    IsClosedImmersion (immersion k n) :=
  IsClosedImmersion.spec_of_surjective _ (Function.surjective_eval n)

/-- The morphism `f_n` as a morphism of schemes over `S`. -/
def immersionOver (k : Type u) [Field k] (n : ℕ) :
    Over.mk (𝟙 (base k)) ⟶ cover k :=
  Over.homMk (immersion k n) (immersion_comp_cover_hom k n)

/-- The underlying scheme morphism of `immersionOver k n` is `immersion k n`. -/
theorem immersionOver_left (k : Type u) [Field k] (n : ℕ) :
    (immersionOver k n).left = immersion k n := sorry

/-- The `i`-th summand of the relation scheme: the cover on the diagonal index, and a copy of
`S` on each off-diagonal index. -/
def relationComponent (k : Type u) [Field k] : relationIndex → Over (base k)
  | none => cover k
  | some _ => Over.mk (𝟙 (base k))

/-- The diagonal summand of the relation is the cover `U`. -/
theorem relationComponent_none (k : Type u) [Field k] :
    relationComponent k none = cover k := sorry

/-- An off-diagonal summand of the relation is a copy of `S` over `S`. -/
theorem relationComponent_some (k : Type u) [Field k] (p : offDiagonal) :
    relationComponent k (some p) = Over.mk (𝟙 (base k)) := sorry

/-- The component of `j` on the summand indexed by `i`: the relative diagonal on `U`, and
`(f_n, f_m)` on the copy of `S` indexed by `(n, m)`. -/
def relationComponentHom (k : Type u) [Field k] :
    (i : relationIndex) → relationComponent k i ⟶ cover k ⨯ cover k
  | none => prod.lift (𝟙 (cover k)) (𝟙 (cover k))
  | some p => prod.lift (immersionOver k p.1.1) (immersionOver k p.1.2)

/-- On the diagonal summand, `j` is the relative diagonal of `U` over `S`. -/
theorem relationComponentHom_none (k : Type u) [Field k] :
    relationComponentHom k none = prod.lift (𝟙 (cover k)) (𝟙 (cover k)) := sorry

/-- On the `(n, m)` summand, `j` is the pair `(f_n, f_m)`. -/
theorem relationComponentHom_some (k : Type u) [Field k] (p : offDiagonal) :
    relationComponentHom k (some p) =
      prod.lift (immersionOver k p.1.1) (immersionOver k p.1.2) := sorry

/-- The relation scheme `R = U ⨿ ∐_{n ≠ m} S` as an object over `S`. -/
def relationOver (k : Type u) [Field k] : Over (base k) :=
  ∐ relationComponent k

/-- The underlying scheme of `relationOver` is the coproduct of the relation summands. -/
theorem relationOver_eq (k : Type u) [Field k] :
    relationOver k = ∐ relationComponent k := sorry

/-- The morphism `j : R ⟶ U ×_S U` equal to `Δ_{U/S}` on the `U` summand and to
`(f_n, f_m)` on the `(n, m)` summand. -/
def relationHom (k : Type u) [Field k] : relationOver k ⟶ cover k ⨯ cover k :=
  Sigma.desc (relationComponentHom k)

/-- The defining map of the relation is the coproduct fold of the component maps. -/
theorem relationHom_eq (k : Type u) [Field k] :
    relationHom k = Sigma.desc (relationComponentHom k) := sorry

/-- The pre-relation on `U` over `S` with source `R` and defining map `j`. -/
def preRelation (k : Type u) [Field k] : Scheme.PreRelation (cover k) :=
  Scheme.PreRelation.ofHom (relationHom k)

/-- The defining arrow of `preRelation k` is `relationHom k`. -/
theorem preRelation_hom (k : Type u) [Field k] :
    (preRelation k).hom = relationHom k := sorry

/-- The first projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_t_none (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) none ≫ (preRelation k).t = 𝟙 (cover k) := sorry

/-- The second projection of the relation, restricted to the diagonal summand, is the identity. -/
theorem preRelation_s_none (k : Type u) [Field k] :
    Sigma.ι (relationComponent k) none ≫ (preRelation k).s = 𝟙 (cover k) := sorry

/-- The first projection of the relation, restricted to the `(n, m)` summand, is `f_n`. -/
theorem preRelation_t_some (k : Type u) [Field k] (p : offDiagonal) :
    Sigma.ι (relationComponent k) (some p) ≫ (preRelation k).t = immersionOver k p.1.1 := sorry

/-- The second projection of the relation, restricted to the `(n, m)` summand, is `f_m`. -/
theorem preRelation_s_some (k : Type u) [Field k] (p : offDiagonal) :
    Sigma.ι (relationComponent k) (some p) ≫ (preRelation k).s = immersionOver k p.1.2 := sorry

/-- The two projections of `j` are étale and `j` is an equivalence relation. -/
instance instIsEtaleEquivalenceRelation_preRelation (k : Type u) [Field k] :
    (preRelation k).IsEtaleEquivalenceRelation := sorry

/-- The open point `u_n ∈ |U|` corresponding to the immersion `f_n`. -/
def openPoint (k : Type u) [Field k] (n : ℕ) : (cover k).left :=
  immersion k n (IsLocalRing.closedPoint k)

/-- The point `u_n` lies in the image of `f_n`. -/
theorem openPoint_mem_range_immersion (k : Type u) [Field k] (n : ℕ) :
    openPoint k n ∈ Set.range (immersion k n) := sorry

/-- The ideal of finitely supported sequences in the infinite product. -/
def finiteSupportIdeal (k : Type u) [Field k] : Ideal (ℕ → k) :=
  Ideal.span (Set.range fun n : ℕ ↦ Pi.single n (1 : k))

/-- Membership in the finite-support ideal is finite support of the sequence. -/
theorem finiteSupportIdeal_mem_iff {k : Type u} [Field k] (x : ℕ → k) :
    x ∈ finiteSupportIdeal k ↔ (Function.support x).Finite := sorry

end AlgebraicGeometry.AlgebraicSpace.InfiniteProduct
