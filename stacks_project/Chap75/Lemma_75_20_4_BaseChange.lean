module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap81.Lemma_81_10_5_Adjunction

/-!
# Tor-independent derived base change on algebraic spaces

A commutative square of algebraic spaces induces the unbounded derived mate
`Lg^* Rf_* ⟶ Rf'_* L(g')^*`. When the square is cartesian, `f` is quasi-compact
and quasi-separated, and `X` and `Y'` are Tor independent over `Y`, every
component of this mate on `D_QCoh(𝒪_X)` is an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical comparison from iterated derived pullback to derived pullback along
the composite morphism. -/
noncomputable def modulePullbackDerived.compComparison {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X) :
    modulePullbackDerived g ⋙ modulePullbackDerived f ⟶
      modulePullbackDerived (f ≫ g) :=
  Functor.LeftDerived.Homotopy.Composition.comparison
    (Modules.pullback f) (Modules.pullback g) (Modules.pullback (f ≫ g))
    (Modules.pullbackComp f g).symm

/-- The composition comparison is the total-left-derived composition comparison of
module pullbacks. -/
theorem modulePullbackDerived.compComparison_eq {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X) :
    modulePullbackDerived.compComparison f g =
      Functor.LeftDerived.Homotopy.Composition.comparison
        (Modules.pullback f) (Modules.pullback g) (Modules.pullback (f ≫ g))
        (Modules.pullbackComp f g).symm :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The source functor `Rf_* ⋙ Lg^*` of unbounded derived base change. -/
abbrev source (f : X ⟶ Y) (g : Y' ⟶ Y) :
    ModuleDerived X ⥤ ModuleDerived Y' :=
  Modules.pushforwardDerived f ⋙ modulePullbackDerived g

/-- The source functor is derived pushforward along `f` followed by derived pullback
along `g`. -/
theorem source_eq (f : X ⟶ Y) (g : Y' ⟶ Y) :
    source f g = Modules.pushforwardDerived f ⋙ modulePullbackDerived g :=
  sorry

/-- The target functor `L(g')^* ⋙ Rf'_*` of unbounded derived base change. -/
abbrev target (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    ModuleDerived X ⥤ ModuleDerived Y' :=
  modulePullbackDerived g' ⋙ Modules.pushforwardDerived f'

/-- The target functor is derived pullback along `g'` followed by derived pushforward
along `f'`. -/
theorem target_eq (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    target g' f' = modulePullbackDerived g' ⋙ Modules.pushforwardDerived f' :=
  sorry

variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [IsIso (modulePullbackDerived.compComparison f' g)]
variable [IsIso (modulePullbackDerived.compComparison g' f)]

/-- The derived pullback square obtained from invertibility of the two composition
comparisons and the square equality `g' ≫ f = f' ≫ g`. -/
noncomputable def pullbackCartesianIso (sq : CommSq g' f' f g) :
    modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g' :=
  asIso (modulePullbackDerived.compComparison f' g) ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ modulePullbackDerived h) sq.w.symm) ≪≫
    (asIso (modulePullbackDerived.compComparison g' f)).symm

/-- The cartesian derived identification is the composition comparison along `f' ≫ g`,
the equality `sq.w`, and the inverse composition comparison along `g' ≫ f`. -/
theorem pullbackCartesianIso_hom (sq : CommSq g' f' f g) :
    (pullbackCartesianIso sq).hom =
      modulePullbackDerived.compComparison f' g ≫
        eqToHom (congrArg (fun h : X' ⟶ Y ↦ modulePullbackDerived h) sq.w.symm) ≫
          inv (modulePullbackDerived.compComparison g' f) :=
  sorry

/-- The canonical unbounded derived base-change transformation associated to a
commutative square of algebraic spaces. -/
noncomputable def map (sq : CommSq g' f' f g) :
    source f g ⟶ target g' f' :=
  CategoryTheory.DerivedBaseChange.map
    (modulePullbackDerivedPushforwardAdjunction f)
    (modulePullbackDerivedPushforwardAdjunction f')
    (pullbackCartesianIso sq)

/-- The component of the unbounded derived base-change transformation at a derived
module. -/
noncomputable abbrev app (sq : CommSq g' f' f g) (E : ModuleDerived X) :
    (source f g).obj E ⟶ (target g' f').obj E :=
  (map sq).app E

/-- The algebraic-space derived base-change transformation is the categorical right
mate of the derived pullback square. -/
theorem map_eq (sq : CommSq g' f' f g) :
    map sq =
      CategoryTheory.DerivedBaseChange.map
        (modulePullbackDerivedPushforwardAdjunction f)
        (modulePullbackDerivedPushforwardAdjunction f')
        (pullbackCartesianIso sq) :=
  sorry

/-- Transposing the canonical derived base-change component recovers the square
comparison followed by the derived pullback of the counit. -/
theorem map_spec (sq : CommSq g' f' f g) (E : ModuleDerived X) :
    ((modulePullbackDerivedPushforwardAdjunction f').homEquiv
        ((source f g).obj E) ((modulePullbackDerived g').obj E)).symm (app sq E) =
      (pullbackCartesianIso sq).hom.app ((Modules.pushforwardDerived f).obj E) ≫
        (modulePullbackDerived g').map
          ((modulePullbackDerivedPushforwardAdjunction f).counit.app E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- For a Tor-independent cartesian square whose vertical map is quasi-compact and
quasi-separated, every component of the canonical unbounded derived base-change
transformation on a derived module with quasi-coherent cohomology is invertible. -/
theorem map_app_isIso (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : IsPullback g' f' f g)
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (E : DerivedQCoh X) :
    IsIso ((Hom.DerivedBaseChange.map sq.toCommSq).app E.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange
