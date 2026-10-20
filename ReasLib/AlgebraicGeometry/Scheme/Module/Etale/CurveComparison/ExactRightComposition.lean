/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.MappedResolutionComparison
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace ActualExactRightComposition
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
variable [Abelian A] [Abelian B] [Abelian C] [HasInjectiveResolutions A] [HasInjectiveResolutions B]
variable (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The composition comparison uses actual source and target resolutions and
the recursively constructed injective lift. F is exact; injective preservation is not assumed. -/
def app (M : A) (n : ℕ) : ((F ⋙ G).rightDerived n).obj M ⟶
    (G.rightDerived n).obj (F.obj M) :=
  let I := injectiveResolution M
  let J := injectiveResolution (F.obj M)
  (I.isoRightDerivedObj (F ⋙ G) n).hom ≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) n).map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℕ)).inv.app I.cocomplex ≫
        (G.mapHomologicalComplex (ComplexShape.up ℕ)).map (ActualMappedResolution.map F I J)) ≫
    (J.isoRightDerivedObj G n).inv

/-- Naturality follows from comparison homotopies between the specified injective lifts. -/
theorem app_naturality {M N : A} (a : M ⟶ N) (n : ℕ) :
    ((F ⋙ G).rightDerived n).map a ≫ app F G N n =
      app F G M n ≫ (G.rightDerived n).map (F.map a) := sorry

/-- The canonical natural composition comparison for exact precomposition. -/
def comparison (n : ℕ) : (F ⋙ G).rightDerived n ⟶ F ⋙ G.rightDerived n where
  app M := app F G M n
  naturality := fun _ _ a ↦ app_naturality F G a n

/-- The specified comparison is invertible if the exact image of every source
injective is G-acyclic. This is a proof criterion, not extra comparison data. -/
theorem comparison_isIso
    (hacyclic : ∀ I : A, Injective I → ∀ n : ℕ, IsZero ((G.rightDerived (n + 1)).obj (F.obj I)))
    (n : ℕ) : IsIso (comparison F G n) := sorry

/-- Invert only the specified comparison when its actual acyclicity criterion holds. -/
def isoOfAcyclic
    (hacyclic : ∀ I : A, Injective I → ∀ n : ℕ, IsZero ((G.rightDerived (n + 1)).obj (F.obj I)))
    (n : ℕ) :=
  @asIso _ _ _ _ (comparison F G n) (comparison_isIso F G hacyclic n)

end ActualExactRightComposition
