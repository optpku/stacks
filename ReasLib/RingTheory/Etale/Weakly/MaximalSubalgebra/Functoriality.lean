/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Pi
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import ReasLib.RingTheory.Etale.Weakly.Field.Consequences
public import ReasLib.RingTheory.Etale.Weakly.MaximalSubalgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of the maximal weakly etale subalgebra

Over a field, the maximal weakly etale subalgebra is functorial, preserves filtered colimits,
ignores nilpotents, and commutes with finite products.

@stack 0CKT
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x

namespace Subalgebra.maximalWeaklyEtale

variable {K : Type u} [Field K]
variable {A' : Type v} [CommRing A'] [Algebra K A']
variable {A : Type w} [CommRing A] [Algebra K A]

/-- The image of the maximal weakly etale subalgebra under an algebra map lies in the maximal
weakly etale subalgebra of the target. -/
@[stacks 0CKT "(1), image containment"]
theorem map_le (f : A' →ₐ[K] A) :
    (Subalgebra.maximalWeaklyEtale K A').map f ≤ Subalgebra.maximalWeaklyEtale K A := sorry

/-- An element of the source maximal weakly etale subalgebra maps into the target one. -/
@[stacks 0CKT "(1), elementwise image containment"]
theorem map_mem (f : A' →ₐ[K] A) (a : Subalgebra.maximalWeaklyEtale K A') :
    f a ∈ Subalgebra.maximalWeaklyEtale K A := sorry

/-- Lemma 15.106.3 (1), Stacks `0CKT`: the algebra map induced on maximal weakly etale
subalgebras. -/
@[stacks 0CKT "(1), induced algebra map"]
def map (f : A' →ₐ[K] A) :
    Subalgebra.maximalWeaklyEtale K A' →ₐ[K] Subalgebra.maximalWeaklyEtale K A :=
  (f.comp (Subalgebra.maximalWeaklyEtale K A').val).codRestrict
    (Subalgebra.maximalWeaklyEtale K A) (map_mem f)

/-- The induced map agrees with the ambient algebra map on elements. -/
@[stacks 0CKT "(1), induced map on elements"]
theorem map_apply (f : A' →ₐ[K] A) (a : Subalgebra.maximalWeaklyEtale K A') :
    (map f a : A) = f a := sorry

section Functor

variable {X Y Z : CommAlgCat.{v} K}

/-- The induced map respects identity morphisms. -/
theorem map_id (X : CommAlgCat.{v} K) :
    CommAlgCat.ofHom (map (AlgHom.id K X)) =
      𝟙 (CommAlgCat.of K (Subalgebra.maximalWeaklyEtale K X)) := sorry

/-- The induced map respects composition. -/
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    CommAlgCat.ofHom (map (f ≫ g).hom) =
      CommAlgCat.ofHom (map f.hom) ≫ CommAlgCat.ofHom (map g.hom) := sorry

/-- The maximal weakly etale subalgebra construction as an endofunctor on commutative
`K`-algebras. -/
@[stacks 0CKT "(1), maximal weakly etale subalgebra functor"]
def functor (K : Type u) [Field K] : CommAlgCat.{v} K ⥤ CommAlgCat.{v} K where
  obj X := CommAlgCat.of K (Subalgebra.maximalWeaklyEtale K X)
  map f := CommAlgCat.ofHom (map f.hom)
  map_id X := map_id X
  map_comp f g := map_comp f g

end Functor

/-- Lemma 15.106.3 (2), Stacks `0CKT`: for an injective algebra map, the source maximal weakly
etale subalgebra is the comap of the target one. -/
@[stacks 0CKT "(2), intersection with a subalgebra"]
theorem comap_of_injective (f : A' →ₐ[K] A) (hf : Function.Injective f) :
    Subalgebra.maximalWeaklyEtale K A' =
      (Subalgebra.maximalWeaklyEtale K A).comap f := sorry

/-- Lemma 15.106.3 (3), Stacks `0CKT`: the maximal weakly etale subalgebra functor preserves
filtered colimits. -/
@[stacks 0CKT "(3), filtered colimits"]
theorem preservesFilteredColimits (K : Type u) [Field K] :
    PreservesFilteredColimits (functor K) := sorry

/-- Directed-union specialization of preservation of filtered colimits. -/
@[stacks 0CKT "(3), directed unions"]
theorem eq_sSup_of_directed
    {ι : Type x} (S : ι → Subalgebra K A)
    (hS : Directed (· ≤ ·) S) (hA : sSup (Set.range S) = ⊤) :
    Subalgebra.maximalWeaklyEtale K A =
      sSup (Set.range fun i ↦
        (Subalgebra.maximalWeaklyEtale K (S i)).map (S i).val) := sorry

/-- The canonical map to the maximal weakly etale subalgebra of the reduction. -/
@[stacks 0CKT "(4), reduction map"]
def reductionMap (K : Type u) [Field K] (A : Type w) [CommRing A] [Algebra K A] :
    Subalgebra.maximalWeaklyEtale K A →ₐ[K]
      Subalgebra.maximalWeaklyEtale K (A ⧸ nilradical A) :=
  map (Ideal.Quotient.mkₐ K (nilradical A))

/-- Lemma 15.106.3 (4), Stacks `0CKT`: the reduction map is bijective. -/
@[stacks 0CKT "(4), invariance under reduction"]
theorem reductionMap_bijective : Function.Bijective (reductionMap K A) := sorry

/-- Lemma 15.106.3 (5), Stacks `0CKT`: maximal weakly etale subalgebras commute with finite
products. -/
@[stacks 0CKT "(5), finite products"]
theorem pi {ι : Type x} [Finite ι] (R : ι → Type v)
    [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)] :
    Subalgebra.maximalWeaklyEtale K ((i : ι) → R i) =
      Subalgebra.pi Set.univ (fun i ↦ Subalgebra.maximalWeaklyEtale K (R i)) := sorry

/-- Lemma 15.106.3 (6), Stacks `0CKT`: if the ambient algebra has only trivial idempotents, its
maximal weakly etale subalgebra is a field. -/
@[stacks 0CKT "(6), field criterion"]
theorem isField_of_idempotents [Nontrivial A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField (Subalgebra.maximalWeaklyEtale K A) := sorry

/-- Lemma 15.106.3 (7), Stacks `0CKT`: under the same idempotent hypothesis, the maximal weakly
etale subalgebra is separable over the base field. -/
@[stacks 0CKT "(7), separability"]
theorem isSeparable_of_idempotents [Nontrivial A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Algebra.IsSeparable K (Subalgebra.maximalWeaklyEtale K A) := sorry

/-- The separability conclusion implies algebraicity of the maximal weakly etale subalgebra. -/
@[stacks 0CKT "(7), algebraicity"]
theorem isAlgebraic_of_idempotents [Nontrivial A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Algebra.IsAlgebraic K (Subalgebra.maximalWeaklyEtale K A) := sorry

end Subalgebra.maximalWeaklyEtale
