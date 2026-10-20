module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
public import ReasLib.RingTheory.RingHom.TorDimension
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AffineSpectrum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.InternalHom.TorIndependence

/-! # Affine spectra and derived internal-Hom base change

Typed compatibility checks for the shared affine-spectrum morphism and the legacy
strong-monoidal interface to the internal-Hom base-change construction.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalClosed CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

#check (specMap : ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B),
  ofOver (Over.mk (Spec.map φ)) ⟶ ofOver (Over.mk (𝟙 (Spec A))))

#check (specMap_eq : ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B),
  specMap φ = ofOverHomMk (Spec.map φ) (Category.comp_id (Spec.map φ)))

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

section

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
variable [(modulePullbackDerived g').Monoidal]

/-- The derived internal-Hom base-change map associated to the monoidal derived pullback. -/
noncomputable def map (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M K : ModuleDerived X) :
    (source f g).obj ((H_X.ihomOf M).obj K) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).obj
          ((modulePullbackDerived g').obj K)) :=
  mapOfTensorIso sq H_X H_X'
    (fun A B ↦ (Functor.Monoidal.μIso (modulePullbackDerived g') A B).symm) M K

/-- Internal-Hom base change is base change followed by pushforward of the monoidal
pullback/internal-Hom comparison. -/
theorem map_spec (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M K : ModuleDerived X) :
    map sq H_X H_X' M K =
      (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
        (Modules.moduleDerivedPushforward f').map
          (Functor.PullbackInternalHom.comparisonOf H_X H_X'
            (modulePullbackDerived g')
            (fun A B ↦ (Functor.Monoidal.μIso (modulePullbackDerived g') A B).symm)
            M K) := rfl

end

#check (map :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
      [(modulePullbackDerived g').Monoidal]
    (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M K : ModuleDerived X),
    (source f g).obj ((H_X.ihomOf M).obj K) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).obj
          ((modulePullbackDerived g').obj K)))

#check (map_spec :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
      [(modulePullbackDerived g').Monoidal]
    (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M K : ModuleDerived X),
    map sq H_X H_X' M K =
      (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
        (Modules.moduleDerivedPushforward f').map
          (Functor.PullbackInternalHom.comparisonOf H_X H_X'
            (modulePullbackDerived g')
            (fun A B ↦ (Functor.Monoidal.μIso (modulePullbackDerived g') A B).symm)
            M K))

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

