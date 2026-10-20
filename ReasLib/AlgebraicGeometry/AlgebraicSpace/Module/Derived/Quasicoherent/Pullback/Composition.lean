module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Composition of derived pullbacks with quasi-coherent cohomology -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- The canonical composition comparison restricted to quasi-coherent cohomology. -/
def pullbackCompMap {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : DerivedQCoh Z) :
    (pullback f).obj ((pullback g).obj E) ⟶ (pullback (f ≫ g)).obj E :=
  ObjectProperty.homMk ((ModuleDerived.pullbackCompComparison f g).app E.obj)

/-- Forgetting quasi-coherent cohomology recovers the canonical ambient comparison. -/
theorem pullbackCompMap_hom {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (E : DerivedQCoh Z) :
    (pullbackCompMap f g E).hom =
      (ModuleDerived.pullbackCompComparison f g).app E.obj := rfl

/-- Iterated derived pullback is canonically isomorphic to pullback along the composite. -/
def pullbackCompAppIso {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X)
    (K : DerivedQCoh X) :
    (pullback f).obj ((pullback g).obj K) ≅ (pullback (f ≫ g)).obj K :=
  (derivedQuasiCoherentModuleProperty Y).fullyFaithfulι.preimageIso
    ((ModuleDerived.pullbackCompIso f g).app K.obj)

/-- The forward composition isomorphism is the canonical restricted comparison map. -/
theorem pullbackCompAppIso_hom {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X)
    (K : DerivedQCoh X) :
    (pullbackCompAppIso f g K).hom = pullbackCompMap f g K :=
  sorry

/-- The two iterated derived pullbacks around a commutative square are canonically
isomorphic. -/
def pullbackSquareAppIso {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : CommSq g' f' f g) (K : DerivedQCoh Y) :
    (pullback g').obj ((pullback f).obj K) ≅
      (pullback f').obj ((pullback g).obj K) :=
  pullbackCompAppIso g' f K ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ (pullback h).obj K) sq.w) ≪≫
    (pullbackCompAppIso f' g K).symm

/-- The square comparison composes the two composition comparisons with the equality
of the composite morphisms. -/
theorem pullbackSquareAppIso_hom {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : CommSq g' f' f g) (K : DerivedQCoh Y) :
    (pullbackSquareAppIso g' f' f g sq K).hom =
      (pullbackCompAppIso g' f K).hom ≫
        (eqToIso (congrArg (fun h : X' ⟶ Y ↦ (pullback h).obj K) sq.w)).hom ≫
          (pullbackCompAppIso f' g K).inv :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
