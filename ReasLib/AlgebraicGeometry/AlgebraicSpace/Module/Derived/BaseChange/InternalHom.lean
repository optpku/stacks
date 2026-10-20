module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.InternalHom
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison

/-! # Internal-Hom base change for algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.MonoidalClosed CategoryTheory.Functor CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]

/-- The derived internal-Hom base-change morphism associated to a commutative square of
algebraic spaces with an explicit tensor comparison: apply unbounded derived base change
to `ihomOf M K`, then push forward the pullback/internal-Hom comparison along `L(g')^*`. -/
noncomputable def mapOfTensorIso (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (tensorIso : ∀ A B : ModuleDerived X,
      (LeftDerived.Homotopy.functor (Modules.pullback g')).obj (A ⊗ B) ≅
        (LeftDerived.Homotopy.functor (Modules.pullback g')).obj A ⊗
          (LeftDerived.Homotopy.functor (Modules.pullback g')).obj B)
    (M K : ModuleDerived X) :
    (source f g).obj ((H_X.ihomOf M).obj K) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj
          ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj K)) :=
  (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
    (Modules.moduleDerivedPushforward f').map
      (Functor.PullbackInternalHom.comparisonOf H_X H_X'
        (LeftDerived.Homotopy.functor (Modules.pullback g'))
        tensorIso
        M K)

/-- The algebraic-space internal-Hom base-change morphism is the derived base-change
component at `ihomOf M K` followed by derived pushforward of the pullback/internal-Hom
comparison. -/
theorem mapOfTensorIso_spec (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (tensorIso : ∀ A B : ModuleDerived X,
      (LeftDerived.Homotopy.functor (Modules.pullback g')).obj (A ⊗ B) ≅
        (LeftDerived.Homotopy.functor (Modules.pullback g')).obj A ⊗
          (LeftDerived.Homotopy.functor (Modules.pullback g')).obj B)
    (M K : ModuleDerived X) :
    mapOfTensorIso sq H_X H_X' tensorIso M K =
      (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
        (Modules.moduleDerivedPushforward f').map
          (Functor.PullbackInternalHom.comparisonOf H_X H_X'
            (LeftDerived.Homotopy.functor (Modules.pullback g'))
            tensorIso
            M K) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom


namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]

/-- The canonical internal-Hom base-change map composes derived base change at internal Hom
with pushforward of the comparison obtained by transposing pulled-back evaluation. -/
def canonicalMap (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M K : ModuleDerived X) :
    (source f g).obj ((H_X.ihomOf M).obj K) ⟶
      (Modules.moduleDerivedPushforward f').obj
        ((H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj
          ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj K)) :=
  (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
    (Modules.moduleDerivedPushforward f').map
      (ModuleDerived.InternalHom.pullbackComparison g' H_X H_X' T_X T_X' M K)

/-- The canonical internal-Hom base-change map is the derived base-change component followed
by pushforward of the canonical pullback/internal-Hom comparison. -/
theorem canonicalMap_spec (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M K : ModuleDerived X) :
    canonicalMap sq H_X H_X' T_X T_X' M K =
      (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
        (Modules.moduleDerivedPushforward f').map
          (ModuleDerived.InternalHom.pullbackComparison g' H_X H_X' T_X T_X' M K) := rfl

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom
