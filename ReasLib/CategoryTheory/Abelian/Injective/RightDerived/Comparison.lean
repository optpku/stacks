/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# One-way comparison for precomposition of right derived functors
-/

@[expose] public section

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C]
variable (G : A ⥤ B) [G.Additive] [G.PreservesInjectiveObjects]
variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]

/-- The augmentation mapped by an injective-preserving functor extends to degree zero
of an injective resolution of its image object. -/
def precompResolutionMapZero (X : A) :
    (injectiveResolution (G.obj X)).cocomplex.X 0 ⟶
      G.obj ((injectiveResolution X).cocomplex.X 0) :=
  -- Local instance justification (proof-local temporary data): needed only for this factorization.
  letI : Injective (G.obj ((injectiveResolution X).cocomplex.X 0)) :=
    G.injective_obj_of_injective ((injectiveResolution X).injective 0)
  @Injective.factorThru B _ (G.obj ((injectiveResolution X).cocomplex.X 0))
    (G.obj X) ((injectiveResolution (G.obj X)).cocomplex.X 0) inferInstance
    (G.map ((injectiveResolution X).ι.f 0)) ((injectiveResolution (G.obj X)).ι.f 0)
    (InjectiveResolution.instMonoFNatι (injectiveResolution (G.obj X)) 0)

/-- The degree-zero extension followed by the mapped differential annihilates
the source augmentation. -/
theorem precompResolutionMap_zero_cycle (X : A) :
    (injectiveResolution (G.obj X)).ι.f 0 ≫
        (precompResolutionMapZero G X ≫ G.map ((injectiveResolution X).cocomplex.d 0 1)) =
      0 := sorry

/-- The first extension across the exact source resolution takes values in the mapped
degree-one injective object. -/
def precompResolutionMapOne (X : A) :
    (injectiveResolution (G.obj X)).cocomplex.X 1 ⟶
      G.obj ((injectiveResolution X).cocomplex.X 1) :=
  -- Local instance justification (proof-local temporary data): needed only for this extension.
  letI : Injective (G.obj ((injectiveResolution X).cocomplex.X 1)) :=
    G.injective_obj_of_injective ((injectiveResolution X).injective 1)
  (injectiveResolution (G.obj X)).exact₀.descToInjective
      (precompResolutionMapZero G X ≫ G.map ((injectiveResolution X).cocomplex.d 0 1))
      (precompResolutionMap_zero_cycle G X)

/-- A commutative square of resolution maps makes the next composite annihilate
the preceding source differential. -/
theorem precompResolutionMap_succ_cycle (X : A) (degree : ℕ)
    (first : (injectiveResolution (G.obj X)).cocomplex.X degree ⟶
      G.obj ((injectiveResolution X).cocomplex.X degree))
    (second : (injectiveResolution (G.obj X)).cocomplex.X (degree + 1) ⟶
      G.obj ((injectiveResolution X).cocomplex.X (degree + 1)))
    (comm : first ≫ G.map ((injectiveResolution X).cocomplex.d degree (degree + 1)) =
      (injectiveResolution (G.obj X)).cocomplex.d degree (degree + 1) ≫ second) :
    (injectiveResolution (G.obj X)).cocomplex.d degree (degree + 1) ≫
        (second ≫ G.map ((injectiveResolution X).cocomplex.d (degree + 1) (degree + 2))) =
      0 := sorry

/-- The chosen resolution of `G.obj X` maps to `G` applied degreewise to the chosen
resolution of `X`, extending the mapped augmentation without an exactness assumption. -/
def precompResolutionMap (X : A) :
    (injectiveResolution (G.obj X)).cocomplex ⟶
      (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex :=
  CochainComplex.mkHom _ _ (precompResolutionMapZero G X) (precompResolutionMapOne G X)
    ((injectiveResolution (G.obj X)).exact₀.comp_descToInjective _
      (precompResolutionMap_zero_cycle G X)).symm
    (fun degree maps =>
      -- Local instance justification (proof-local temporary data): needed only for this extension.
      letI : Injective
          (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution X).cocomplex).X (degree + 2)) :=
        G.injective_obj_of_injective ((injectiveResolution X).injective (degree + 2))
      ⟨((injectiveResolution (G.obj X)).exact_succ degree).descToInjective
            (maps.2.1 ≫ G.map ((injectiveResolution X).cocomplex.d (degree + 1) (degree + 2)))
            (precompResolutionMap_succ_cycle G X degree maps.1 maps.2.1 maps.2.2),
        (((injectiveResolution (G.obj X)).exact_succ degree).comp_descToInjective _
            (precompResolutionMap_succ_cycle G X degree maps.1 maps.2.1 maps.2.2)).symm⟩)

/-- The comparison of resolutions extends the mapped augmentation in degree zero. -/
theorem precompResolutionMap_comm (X : A) :
    (injectiveResolution (G.obj X)).ι.f 0 ≫ (precompResolutionMap G X).f 0 =
      G.map ((injectiveResolution X).ι.f 0) := sorry

variable (F : B ⥤ C) [F.Additive]

/-- Applying an additive functor and homology to the resolution comparison gives
the map from derivation after precomposition to derivation of the composite. -/
def precompComparisonApp (degree : ℕ) (X : A) :
    (G ⋙ F.rightDerived degree).obj X ⟶ ((G ⋙ F).rightDerived degree).obj X :=
  ((injectiveResolution (G.obj X)).isoRightDerivedObj F degree).hom ≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) degree).map
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (precompResolutionMap G X)) ≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) degree).map
      ((mapHomologicalComplexCompIso (Iso.refl (G ⋙ F)) (ComplexShape.up ℕ)).hom.app
        (injectiveResolution X).cocomplex) ≫
    ((injectiveResolution X).isoRightDerivedObj (G ⋙ F) degree).inv

/-- The precomposition comparison on right derived objects is natural. -/
theorem precompComparison_naturality (degree : ℕ) {X Y : A} (morphism : X ⟶ Y) :
    (G ⋙ F.rightDerived degree).map morphism ≫ precompComparisonApp G F degree Y =
      precompComparisonApp G F degree X ≫ ((G ⋙ F).rightDerived degree).map morphism := sorry

/-- An additive functor preserving injective objects yields a one-way natural comparison
from precomposing a right derived functor to deriving the composite. -/
def precompComparison (degree : ℕ) :
    G ⋙ F.rightDerived degree ⟶ (G ⋙ F).rightDerived degree where
  app := precompComparisonApp G F degree
  naturality := fun {X Y} morphism => precompComparison_naturality G F degree morphism

end CategoryTheory.Functor.RightDerived

end
