/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Injective.Resolution.ExactMap
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

noncomputable section

open CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace CategoryTheory.Functor.RightDerived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {A' : Type u₃} [Category.{v₃} A'] [Abelian A'] [HasInjectiveResolutions A']
variable {B' : Type u₄} [Category.{v₄} B'] [Abelian B']
variable (F : A ⥤ B) (G : A' ⥤ B') [F.Additive] [G.Additive]
variable (L : A ⥤ A') (T : B ⥤ B') [L.Additive] [T.Additive]
variable [PreservesFiniteLimits L] [PreservesFiniteColimits L]
variable [PreservesFiniteLimits T] [PreservesFiniteColimits T]
variable (α : F ⋙ T ⟶ L ⋙ G) (degree : ℕ)

/-- An additive functor square with exact horizontal functors induces a comparison
on ordinary right derived objects in every degree. -/
def exactSquareApp (X : A) :
    T.obj ((F.rightDerived degree).obj X) ⟶ (G.rightDerived degree).obj (L.obj X) :=
  let sourceResolution := injectiveResolution X
  let targetResolution := injectiveResolution (L.obj X)
  let sourceComplex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    sourceResolution.cocomplex
  T.map (sourceResolution.isoRightDerivedObj F degree).hom ≫
    ((sourceComplex.sc degree).mapHomologyIso T).inv ≫
    (HomologicalComplex.homologyFunctor B' (ComplexShape.up ℕ) degree).map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
          sourceResolution.cocomplex ≫
        (G.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.ExactMap.map L sourceResolution targetResolution)) ≫
    (targetResolution.isoRightDerivedObj G degree).inv

/-- The ordinary derived-square comparison commutes with maps in the source category. -/
theorem exactSquareApp_naturality {X Y : A} (morphism : X ⟶ Y) :
    T.map ((F.rightDerived degree).map morphism) ≫ exactSquareApp F G L T α degree Y =
      exactSquareApp F G L T α degree X ≫ (G.rightDerived degree).map (L.map morphism) := sorry

/-- An additive square with exact horizontal functors induces a natural transformation
between its ordinary right derived functors. -/
def exactSquare : F.rightDerived degree ⋙ T ⟶ L ⋙ G.rightDerived degree where
  app := exactSquareApp F G L T α degree
  naturality := fun _ _ morphism => exactSquareApp_naturality F G L T α degree morphism

end CategoryTheory.Functor.RightDerived
