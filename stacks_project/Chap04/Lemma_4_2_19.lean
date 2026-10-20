module

public import stacks_project.Chap04.Definition_4_2_17
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

variable (F : A ⥤ B)

/- Lemma 4.2.19: equivalence is characterized by a quasi-inverse, equivalently by the canonical
full, faithful, and essentially-surjective predicate. -/
@[stacks 02C3 "equivalence iff full, faithful, and essentially surjective"]
#check (CategoryTheory.Functor.isEquivalence_iff_exists_quasiInverse F :
  F.IsEquivalence ↔
    ∃ G : B ⥤ A, Nonempty (𝟭 A ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 B))

@[stacks 02C3 "equivalence functor has the canonical full-faithful-essentially-surjective owner"]
#check (CategoryTheory.Functor.IsEquivalence F : Prop)
