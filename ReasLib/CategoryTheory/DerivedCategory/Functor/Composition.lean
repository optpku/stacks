module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Composition
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Composition of Derived Functors

Given a composable pair of functors `F : A ⥤ B` and `G : B ⥤ C` localized along
`S : MorphismProperty A` and `S' : MorphismProperty B`, this file constructs the canonical
comparison natural transformations between the total derived functor of the composite
`G ∘ F` and the composite of the individual total derived functors:

* on the right derived side, `R(G ∘ F) ⟶ RG ∘ RF'`, where `F' = F ⋙ S'.Q`;
* on the left derived side, `LG ∘ LF' ⟶ L(G ∘ F)`.

Both comparison morphisms are obtained from the universal property of the total derived
functor (`rightDerivedDesc` / `leftDerivedLift`), and each comes with a factorization lemma
recording the defining equation used to build it.

To assemble these comparisons, the file first records that `mapHomotopyCategory` is
functorial up to canonical isomorphism: applying it to a composite of additive functors
agrees with composing the induced functors on homotopy categories
(`mapHomotopyCategoryCompIso`), and applying it to a natural isomorphism of additive
functors yields a natural isomorphism of induced functors (`mapHomotopyCategoryIso`).

## Main definitions

* `mapHomotopyCategoryCompIso` — the canonical isomorphism
  `(F ⋙ G).mapHomotopyCategory ≅ F.mapHomotopyCategory ⋙ G.mapHomotopyCategory`.
* `mapHomotopyCategoryIso` — transport of a natural isomorphism of additive functors to
  the induced functors on homotopy categories.
* `RightDerived.Composition.comparison` — the comparison morphism
  `R(G ∘ F) ⟶ RG ∘ RF'`.
* `LeftDerived.Composition.comparison` — the comparison morphism
  `LG ∘ LF' ⟶ L(G ∘ F)`.

## Main results

* `RightDerived.Composition.comparison_fac` — the factorization property defining the
  right-derived comparison through the universal property of `R(G ∘ F)`.
* `LeftDerived.Composition.comparison_fac` — the factorization property defining the
  left-derived comparison through the universal property of `L(G ∘ F)`.

## Tags

stacks: 05T2
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

open ComplexShape

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

section HomotopyCategoryComp

variable [Preadditive A] [Preadditive B] [Preadditive C]

/-- The induced functors of a composite additive functor and of the iterated induced
functors agree on each object of the homotopy category. -/
private theorem mapHomotopyCategoryComp_obj_eq
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ (K : HomotopyCategory A (up ℤ)),
      ((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K =
        (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).obj K := by
  rintro ⟨K⟩
  rfl

/-- The induced functors of a composite additive functor and of the iterated induced
functors agree on each morphism of the homotopy category. -/
private theorem mapHomotopyCategoryComp_map_eq
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ =
        (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ := by
  rintro ⟨K⟩ ⟨L⟩ ⟨φ⟩
  rfl


/-- Applying `mapHomotopyCategory` to a natural isomorphism of additive functors yields the
corresponding isomorphism on homotopy categories. -/
noncomputable def mapHomotopyCategoryIso
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      G.mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom (up ℤ)
  inv := NatTrans.mapHomotopyCategory e.inv (up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp]
    simpa using
      congrArg (fun α ↦ NatTrans.mapHomotopyCategory α (up ℤ)) (Iso.hom_inv_id e)
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp]
    simpa using
      congrArg (fun α ↦ NatTrans.mapHomotopyCategory α (up ℤ)) (Iso.inv_hom_id e)

end HomotopyCategoryComp

section Right

variable (S : MorphismProperty A) (S' : MorphismProperty B) (F : A ⥤ B) (G : B ⥤ C)
variable [(F ⋙ G).HasRightDerivedFunctor S]
variable [(F ⋙ S'.Q).HasRightDerivedFunctor S]
variable [G.HasRightDerivedFunctor S']

/-- Let `F' : A ⥤ S'⁻¹B` be the composite `F ⋙ S'.Q`. If the right derived functors of `F'`,
`G`, and `G ∘ F` are everywhere defined, then there is a canonical natural transformation
`R(G ∘ F) ⟶ RG ∘ RF'`. -/
@[stacks 05T2]
noncomputable def RightDerived.Composition.comparison :
    totalRightDerived (F ⋙ G) S.Q S ⟶
      totalRightDerived (F ⋙ S'.Q) S.Q S ⋙ totalRightDerived G S'.Q S' :=
  RightDerived.Composition.comparisonOfModels S
    (totalRightDerivedUnit (F ⋙ S'.Q) S.Q S)
    (totalRightDerivedUnit G S'.Q S')
    (totalRightDerivedUnit (F ⋙ G) S.Q S)

/-- The right-derived comparison morphism factors the canonical unit of `R(G ∘ F)` through the
iterated right derived functor `RG ∘ RF'`. -/
@[reassoc]
theorem RightDerived.Composition.comparison_fac :
    totalRightDerivedUnit (F ⋙ G) S.Q S ≫
        whiskerLeft S.Q (RightDerived.Composition.comparison S S' F G) =
      whiskerLeft F (totalRightDerivedUnit G S'.Q S') ≫
        (associator F S'.Q (totalRightDerived G S'.Q S')).hom ≫
        whiskerRight (totalRightDerivedUnit (F ⋙ S'.Q) S.Q S)
          (totalRightDerived G S'.Q S') ≫
        (associator S.Q (totalRightDerived (F ⋙ S'.Q) S.Q S)
          (totalRightDerived G S'.Q S')).hom := sorry

/-- On components, the canonical right-derived comparison is characterized without explicit
associators: the direct unit followed by comparison is the two-stage unit. -/
@[simp]
theorem RightDerived.Composition.comparison_fac_app (X : A) :
    (totalRightDerivedUnit (F ⋙ G) S.Q S).app X ≫
      (RightDerived.Composition.comparison S S' F G).app (S.Q.obj X) =
        (totalRightDerivedUnit G S'.Q S').app (F.obj X) ≫
          (totalRightDerived G S'.Q S').map
            ((totalRightDerivedUnit (F ⋙ S'.Q) S.Q S).app X) := sorry

/-- The inverse of an invertible right-derived composition comparison satisfies the reverse
factorization equation.  This is the inverse-comparison analogue of
`RightDerived.Composition.comparison_fac`. -/
@[reassoc (attr := simp), stacks 05T2]
theorem RightDerived.Composition.comparison_inv_fac
    [IsIso (RightDerived.Composition.comparison S S' F G)] :
    (whiskerLeft F (totalRightDerivedUnit G S'.Q S') ≫
        (associator F S'.Q (totalRightDerived G S'.Q S')).hom ≫
        whiskerRight (totalRightDerivedUnit (F ⋙ S'.Q) S.Q S)
          (totalRightDerived G S'.Q S') ≫
        (associator S.Q (totalRightDerived (F ⋙ S'.Q) S.Q S)
          (totalRightDerived G S'.Q S')).hom) ≫
      Functor.whiskerLeft S.Q
          (asIso (RightDerived.Composition.comparison S S' F G)).inv =
        totalRightDerivedUnit (F ⋙ G) S.Q S := sorry

/-- Objectwise reverse factorization for an invertible right-derived composition comparison. -/
@[reassoc (attr := simp), stacks 05T2]
theorem RightDerived.Composition.comparison_inv_fac_app
    [IsIso (RightDerived.Composition.comparison S S' F G)] (X : A) :
    (totalRightDerivedUnit G S'.Q S').app (F.obj X) ≫
        (totalRightDerived G S'.Q S').map
          ((totalRightDerivedUnit (F ⋙ S'.Q) S.Q S).app X) ≫
        (asIso (RightDerived.Composition.comparison S S' F G)).inv.app (S.Q.obj X) =
      (totalRightDerivedUnit (F ⋙ G) S.Q S).app X := sorry

attribute [simp] RightDerived.Composition.comparison_fac
  RightDerived.Composition.comparison_fac_assoc

end Right

section Left

variable (S : MorphismProperty A) (S' : MorphismProperty B) (F : A ⥤ B) (G : B ⥤ C)
variable [(F ⋙ G).HasLeftDerivedFunctor S]
variable [(F ⋙ S'.Q).HasLeftDerivedFunctor S]
variable [G.HasLeftDerivedFunctor S']

/-- Let `F' : A ⥤ S'⁻¹B` be the composite `F ⋙ S'.Q`. If the left derived functors of `F'`,
`G`, and `G ∘ F` are everywhere defined, then there is a canonical natural transformation
`LG ∘ LF' ⟶ L(G ∘ F)`, written in Lean as `LF' ⋙ LG ⟶ L(F ⋙ G)`. -/
@[stacks 05T2]
noncomputable def LeftDerived.Composition.comparison :
    totalLeftDerived (F ⋙ S'.Q) S.Q S ⋙ totalLeftDerived G S'.Q S' ⟶
      totalLeftDerived (F ⋙ G) S.Q S :=
  LeftDerived.Composition.comparisonOfModels S
    (totalLeftDerivedCounit (F ⋙ S'.Q) S.Q S)
    (totalLeftDerivedCounit G S'.Q S')
    (totalLeftDerivedCounit (F ⋙ G) S.Q S)

/-- The left-derived comparison morphism factors the counit of the iterated left derived functor
through the canonical counit of `L(G ∘ F)`. -/
@[reassoc]
theorem LeftDerived.Composition.comparison_fac :
    whiskerLeft S.Q (LeftDerived.Composition.comparison S S' F G) ≫
      totalLeftDerivedCounit (F ⋙ G) S.Q S =
        (associator S.Q (totalLeftDerived (F ⋙ S'.Q) S.Q S)
          (totalLeftDerived G S'.Q S')).inv ≫
          whiskerRight (totalLeftDerivedCounit (F ⋙ S'.Q) S.Q S)
            (totalLeftDerived G S'.Q S') ≫
          (associator F S'.Q (totalLeftDerived G S'.Q S')).hom ≫
          whiskerLeft F (totalLeftDerivedCounit G S'.Q S') := sorry

/-- On components, the canonical left-derived comparison followed by the direct counit is the
two-stage counit, without explicit associators. -/
@[simp]
theorem LeftDerived.Composition.comparison_fac_app (X : A) :
    (LeftDerived.Composition.comparison S S' F G).app (S.Q.obj X) ≫
      (totalLeftDerivedCounit (F ⋙ G) S.Q S).app X =
        (totalLeftDerived G S'.Q S').map
            ((totalLeftDerivedCounit (F ⋙ S'.Q) S.Q S).app X) ≫
          (totalLeftDerivedCounit G S'.Q S').app (F.obj X) := sorry

attribute [simp] LeftDerived.Composition.comparison_fac
  LeftDerived.Composition.comparison_fac_assoc

end Left

end

end Functor

end CategoryTheory
