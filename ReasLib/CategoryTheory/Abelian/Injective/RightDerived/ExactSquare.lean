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
    T.obj ((F.rightDerived degree).obj X) ⟶ (G.rightDerived degree).obj (L.obj X) := by
  let sourceResolution := injectiveResolution X
  let targetResolution := injectiveResolution (L.obj X)
  let sourceComplex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    sourceResolution.cocomplex
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
    Functor.mapHomotopyCategory HomotopyCategory.homologyFunctor
  change T.obj ((HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) degree).obj
      sourceComplex) ⟶
    (HomologicalComplex.homologyFunctor B' (ComplexShape.up ℕ) degree).obj
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj targetResolution.cocomplex)
  let targetComplex := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    targetResolution.cocomplex
  let comparison :=
    (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
        sourceResolution.cocomplex ≫
      (G.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (InjectiveResolution.ExactMap.map L sourceResolution targetResolution)
  let hS := (sourceComplex.sc degree).homologyData.left
  let hU := (targetComplex.sc degree).homologyData.left
  let φ : (sourceComplex.sc degree).map T ⟶ targetComplex.sc degree :=
    (HomologicalComplex.shortComplexFunctor B' (ComplexShape.up ℕ) degree).map comparison
  dsimp only [ShortComplex.map] at φ
  have cycle : (T.map hS.i ≫ φ.τ₂) ≫ (targetComplex.sc degree).g = 0 := by
    rw [Category.assoc, φ.comm₂₃, ← Category.assoc, ← T.map_comp,
      hS.wi, T.map_zero, zero_comp]
  let k := hU.liftK (T.map hS.i ≫ φ.τ₂) cycle
  have boundary : T.map hS.f' ≫ k = φ.τ₁ ≫ hU.f' := by
    apply (cancel_mono hU.i).1
    dsimp only [k]
    rw [Category.assoc, hU.liftK_i, ← Category.assoc, ← T.map_comp,
      hS.f'_i, Category.assoc, hU.f'_i]
    exact φ.comm₁₂.symm
  have vanishes : T.map hS.f' ≫ (k ≫ hU.π) = 0 := by
    rw [← Category.assoc, boundary, Category.assoc, hU.f'_π, comp_zero]
  exact (CokernelCofork.mapIsColimit _ hS.hπ' T).desc
    (CokernelCofork.ofπ (k ≫ hU.π) vanishes)

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
