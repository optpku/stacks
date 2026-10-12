/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap75.Lemma_75_21_1_Criteria
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction

/-!
# Cohomology and base change for a single derived quasi-coherent complex

On a cartesian square of algebraic spaces whose vertical morphism is quasi-compact and
quasi-separated, the equivalent conditions of Lemma 75.21.1 make the composite of
canonical derived base change with `Rf'_* α` an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.Adjunction
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Unfolded homotopy-to-derived pullback has a total left derived functor. -/
instance instHasLeftDerivedFunctor_pullback_mapHomotopyCategory
    {Y X : AlgebraicSpace S} (φ : Y ⟶ X) :
    ((Modules.pullback φ).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules X) (up ℤ)) :=
  inferInstanceAs
    ((Functor.Homotopy.toDerived (Modules.pullback φ)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules X) (up ℤ)))

/-- Unfolded homotopy-to-derived pushforward has a total right derived functor. -/
instance instHasRightDerivedFunctor_pushforward_mapHomotopyCategory
    {Y X : AlgebraicSpace S} (φ : Y ⟶ X) :
    ((Modules.pushforward φ).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules Y) (up ℤ)) :=
  inferInstanceAs
    ((Functor.Homotopy.toDerived (Modules.pushforward φ)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules Y) (up ℤ)))

/-- Absolute-derived pair condition for module pullback and pushforward. -/
instance instHasPair_pullbackPushforward {Y X : AlgebraicSpace S} (φ : Y ⟶ X) :
    @TotalDerived.HasPair
      (HomotopyCategory (Modules X) (up ℤ)) (HomotopyCategory (Modules Y) (up ℤ))
      (ModuleDerived X) (ModuleDerived Y) _ _ _ _
      ((Modules.pullback φ).mapHomotopyCategory (up ℤ))
      ((Modules.pushforward φ).mapHomotopyCategory (up ℤ))
      (HomotopyCategory.quasiIso (Modules X) (up ℤ))
      (HomotopyCategory.quasiIso (Modules Y) (up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh _ _ _ _ :=
  sorry

/-- The unbounded derived adjunction `Lf^* ⊣ Rf_*` on `D(𝒪)`. -/
noncomputable def derivedPullbackPushforwardAdjunction {Y X : AlgebraicSpace S}
    (φ : Y ⟶ X) :
    ModuleDerived.pullback φ ⊣ Modules.pushforwardDerived φ :=
  TotalDerived.HasPair.derived
    (mapHomotopyCategoryAdjunction (Modules.pullbackPushforwardAdjunction φ))
    (HomotopyCategory.quasiIso (Modules X) (up ℤ))
    (HomotopyCategory.quasiIso (Modules Y) (up ℤ))

/-- The derived adjunction is the total-derived adjunction of homotopy-level module
pullback and pushforward. -/
theorem derivedPullbackPushforwardAdjunction_eq {Y X : AlgebraicSpace S}
    (φ : Y ⟶ X) :
    derivedPullbackPushforwardAdjunction φ =
      TotalDerived.HasPair.derived
        (mapHomotopyCategoryAdjunction (Modules.pullbackPushforwardAdjunction φ))
        (HomotopyCategory.quasiIso (Modules X) (up ℤ))
        (HomotopyCategory.quasiIso (Modules Y) (up ℤ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The derived pullback square obtained from invertibility of the two composition
comparisons and the square equality `g' ≫ f = f' ≫ g`. -/
noncomputable def cohomologyBaseChangeCartesianIso
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) :
    ModuleDerived.pullback g ⋙ ModuleDerived.pullback f' ≅
      ModuleDerived.pullback f ⋙ ModuleDerived.pullback g' :=
  ModuleDerived.pullbackCompIso f' g ≪≫
    ModuleDerived.pullbackCongr sq.w.symm ≪≫
    (ModuleDerived.pullbackCompIso g' f).symm

/-- The cartesian derived identification is the composition comparison along `f' ≫ g`,
the equality `sq.w`, and the inverse composition comparison along `g' ≫ f`. -/
theorem cohomologyBaseChangeCartesianIso_hom
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) :
    (cohomologyBaseChangeCartesianIso sq).hom =
      ModuleDerived.pullbackCompComparison f' g ≫
        (ModuleDerived.pullbackCongr sq.w.symm).hom ≫
          inv (ModuleDerived.pullbackCompComparison g' f) :=
  sorry

/-- The composition of the derived base-change mate `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`
with `Rf'_* α : Rf'_* L(g')^* K ⟶ Rf'_* K'`. -/
noncomputable def cohomologyBaseChangeComp (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    (Modules.pushforwardDerived f ⋙ ModuleDerived.pullback g).obj ((inclusion X).obj K) ⟶
      (Modules.pushforwardDerived f').obj ((inclusion X').obj K') :=
  (DerivedBaseChange.map
      (derivedPullbackPushforwardAdjunction f)
      (derivedPullbackPushforwardAdjunction f')
      (cohomologyBaseChangeCartesianIso sq)).app ((inclusion X).obj K) ≫
    (Modules.pushforwardDerived f').map α

/-- `cohomologyBaseChangeComp` is the derived base-change mate followed by `Rf'_* α`. -/
theorem cohomologyBaseChangeComp_eq (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    cohomologyBaseChangeComp g' f' f g sq K K' α =
      (DerivedBaseChange.map
          (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f')
          (cohomologyBaseChangeCartesianIso sq)).app ((inclusion X).obj K) ≫
        (Modules.pushforwardDerived f').map α :=
  sorry

/-- Lemma 75.21.2: for a cartesian square of algebraic spaces over a scheme `S`, `K` in
`D_QCoh(𝒪_X)`, and a map `L(g')^* K ⟶ K'` in `D_QCoh(𝒪_{X'})`, if the equivalent
conditions of Lemma 75.21.1 hold and `f` is quasi-compact and quasi-separated, then the
composition `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K ⟶ Rf'_* K'` is an isomorphism. -/
@[stacks 0DKH]
theorem cohomologyBaseChange_comp_isIso (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (h : cohomologyBaseChangeHolds sq K K' α) :
    IsIso (cohomologyBaseChangeComp g' f' f g sq K K' α) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
