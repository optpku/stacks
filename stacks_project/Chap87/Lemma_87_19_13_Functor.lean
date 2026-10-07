module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.InducedCategory
public import ReasLib.RingTheory.Etale.Category
public import stacks_project.Chap87.Lemma_87_19_13_Completion
public import stacks_project.Chap87.Lemma_87_19_13_Over
public import stacks_project.Chap87.Lemma_87_9_10_Map

/-!
# Spf of weak-ideal completions of étale algebras

The functor sending an étale `B`-algebra `A` to `Spf((A)^∧)` over `Spf(B)` is
the concrete data of the identification in Lemma 87.19.13. It is contravariant
on algebra maps, matching the variance of `Spf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- `Spf` of a weakly admissible ring over `S` is a directed affine thickening
colimit. -/
theorem exists_isDirectedAffineThickeningColimit_spf (A : Type u) [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D (spf A hA).obj :=
  sorry

/-- The morphism `Spf((A)^∧) ⟶ Spf(B)` induced by the algebra map
`B → (A)^∧`. -/
def spfMap_weakIdealCompletion (A : Type u) [CommRing A] [Algebra B A] :
    spf (weakIdealCompletion B A) (specHom_weakIdealCompletion hB A) ⟶
      spf B hB :=
  spfMap (algebraMap B (weakIdealCompletion B A)) (continuous_algebraMap B A) rfl

/-- The underlying functor-of-points morphism of `spfMap_weakIdealCompletion`. -/
theorem spfMap_weakIdealCompletion_hom (A : Type u) [CommRing A] [Algebra B A] :
    (spfMap_weakIdealCompletion hB A).hom =
      (spfMap (algebraMap B (weakIdealCompletion B A))
        (continuous_algebraMap B A) rfl).hom :=
  sorry

/-- `Spf((A)^∧) ⟶ Spf(B)` is representable by algebraic spaces and étale when
`A` is an étale `B`-algebra. -/
instance instEtale_spfMap_weakIdealCompletion (A : Type u) [CommRing A]
    [Algebra B A] [Algebra.Etale B A] :
    FormalAlgebraicSpace.Etale (spfMap_weakIdealCompletion hB A).hom :=
  sorry

/-- The morphism `Spf((A')^∧) ⟶ Spf((A)^∧)` induced by a `B`-algebra map
`A →ₐ[B] A'`. -/
def spfMap_weakIdealCompletion_map {A A' : Type u} [CommRing A] [Algebra B A]
    [CommRing A'] [Algebra B A'] (f : A →ₐ[B] A') :
    spf (weakIdealCompletion B A') (specHom_weakIdealCompletion hB A') ⟶
      spf (weakIdealCompletion B A) (specHom_weakIdealCompletion hB A) :=
  spfMap (weakIdealCompletion.map f) (weakIdealCompletion.continuous_map f) sorry

/-- `spfMap_weakIdealCompletion_map f` lies over `Spf(B)`. -/
theorem spfMap_weakIdealCompletion_map_comp {A A' : Type u} [CommRing A]
    [Algebra B A] [CommRing A'] [Algebra B A'] (f : A →ₐ[B] A') :
    spfMap_weakIdealCompletion_map hB f ≫ spfMap_weakIdealCompletion hB A =
      spfMap_weakIdealCompletion hB A' :=
  sorry

/-- The functor sending an étale `B`-algebra `A` to `Spf((A)^∧)` over `Spf(B)`.
It is contravariant on algebra maps, as is `Spf`. -/
def spfEtaleCompletion :
    (CommAlgCat.Etale.{u} B)ᵒᵖ ⥤ AffineEtaleOver (spf B hB).obj where
  obj A :=
    AffineEtaleOver.mk (spfMap_weakIdealCompletion hB A.unop).hom
      (exists_isDirectedAffineThickeningColimit_spf
        (weakIdealCompletion B A.unop) (specHom_weakIdealCompletion hB A.unop))
  map {A A'} f :=
    InducedCategory.homMk
      (MorphismProperty.Over.homMk
        (spfMap_weakIdealCompletion_map hB f.unop.hom.hom).hom sorry)
  map_id := sorry
  map_comp := sorry

/-- The object map of `spfEtaleCompletion` sends `A` to `Spf((A)^∧)` over
`Spf(B)`. -/
theorem spfEtaleCompletion_obj (A : CommAlgCat.Etale.{u} B) :
    ((spfEtaleCompletion hB).obj (op A)).obj.hom =
      (spfMap_weakIdealCompletion hB A).hom :=
  sorry

/-- The morphism map of `spfEtaleCompletion` is `Spf` of the induced map of
completions. -/
theorem spfEtaleCompletion_map {A A' : CommAlgCat.Etale.{u} B} (f : A ⟶ A') :
    ((spfEtaleCompletion hB).map f.op).hom.left =
      (spfMap_weakIdealCompletion_map hB f.hom.hom).hom :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
