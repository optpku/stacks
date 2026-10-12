/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
public import stacks_project.Chap86.«86_3_2_1_Pushforward»
public import stacks_project.Chap86.«86_7_0_1_Pullback»

/-!
# Right-adjoint derived base change on algebraic spaces

A commutative square of algebraic spaces induces the ordinary derived base-change
transformation on `DerivedQCoh`. Its right-adjoint mate is the comparison
`a' ⋙ Rg'_* ⟶ Rg_* ⋙ a`. Cartesian + Tor independence makes that mate invertible.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- Naturality of the ambient derived base-change components after lifting them to
derived objects with quasi-coherent cohomology. -/
theorem map_naturality
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : CommSq g' f' f g) {E F : DerivedQCoh X} (φ : E ⟶ F) :
    (pushforwardCohomologyIn f ⋙ pullback g).map φ ≫
        ObjectProperty.homMk
          ((pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj F) ≫
            (modulePullbackDerived g).map
              ((pushforwardCohomologyIn.inclusionIso f).hom.app F) ≫
            (Hom.DerivedBaseChange.map sq).app F.obj ≫
            (Modules.pushforwardDerived f').map
              ((pullback.inclusionIso g').inv.app F) ≫
            (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj F)) =
      ObjectProperty.homMk
          ((pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj E) ≫
            (modulePullbackDerived g).map
              ((pushforwardCohomologyIn.inclusionIso f).hom.app E) ≫
            (Hom.DerivedBaseChange.map sq).app E.obj ≫
            (Modules.pushforwardDerived f').map
              ((pullback.inclusionIso g').inv.app E) ≫
            (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj E)) ≫
        (pullback g' ⋙ pushforwardCohomologyIn f').map φ :=
  sorry

/-- The canonical derived base-change transformation on complexes with quasi-coherent
cohomology. -/
noncomputable def map
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : CommSq g' f' f g) :
    pushforwardCohomologyIn f ⋙ pullback g ⟶ pullback g' ⋙ pushforwardCohomologyIn f' where
  app E := ObjectProperty.homMk
    ((pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj E) ≫
      (modulePullbackDerived g).map
        ((pushforwardCohomologyIn.inclusionIso f).hom.app E) ≫
      (Hom.DerivedBaseChange.map sq).app E.obj ≫
      (Modules.pushforwardDerived f').map
        ((pullback.inclusionIso g').inv.app E) ≫
      (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj E))
  naturality _ _ φ := map_naturality g' f' f g sq φ

/-- Forgetting quasi-coherent cohomology from the derived base-change map recovers the
canonical ambient derived base-change component. -/
theorem map_app_hom
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : CommSq g' f' f g) (E : DerivedQCoh X) :
    ((map g' f' f g sq).app E).hom =
      (pullback.inclusionIso g).hom.app ((pushforwardCohomologyIn f).obj E) ≫
        (modulePullbackDerived g).map
          ((pushforwardCohomologyIn.inclusionIso f).hom.app E) ≫
        (Hom.DerivedBaseChange.map sq).app E.obj ≫
        (Modules.pushforwardDerived f').map
          ((pullback.inclusionIso g').inv.app E) ≫
        (pushforwardCohomologyIn.inclusionIso f').inv.app ((pullback g').obj E) :=
  sorry

/-- Tor independence makes the canonical base-change transformation on `DerivedQCoh`
invertible. -/
theorem map_isIso_of_torIndependent
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : IsPullback g' f' f g)
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIso (map g' f' f g sq.toCommSq) :=
  sorry

/-- The right-adjoint mate of the canonical derived base-change transformation. -/
noncomputable def rightMate
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a') :
    a' ⋙ pushforwardCohomologyIn g' ⟶ pushforwardCohomologyIn g ⋙ a :=
  conjugateEquiv
    ((pullbackPushforwardCohomologyAdjunction g').comp f'Adj)
    (fAdj.comp (pullbackPushforwardCohomologyAdjunction g))
    (map g' f' f g sq)

/-- Taking the inverse mate of the right-adjoint base-change transformation recovers the
canonical derived base-change transformation. -/
theorem rightMate_mate
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a') :
    (conjugateEquiv
      ((pullbackPushforwardCohomologyAdjunction g').comp f'Adj)
      (fAdj.comp (pullbackPushforwardCohomologyAdjunction g))).symm
        (rightMate g' f' f g sq a a' fAdj f'Adj) =
      map g' f' f g sq :=
  sorry

/-- Invertibility of derived base change transfers canonically to its right-adjoint mate. -/
noncomputable instance rightMateIsIso
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    [IsIso (map g' f' f g sq)] :
    IsIso (rightMate g' f' f g sq a a' fAdj f'Adj) :=
  sorry

/-- For a cartesian square of algebraic spaces, Tor independence makes the
right-adjoint base-change mate invertible. -/
theorem rightMate_isIso_of_torIndependent
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIso (rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

