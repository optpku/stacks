module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap103.Lemma_103_10_1_Adjunction
public import stacks_project.Chap110.Lemma_110_61_3_Pushforward

/-!
# Quasi-coherent higher direct images on algebraic stacks

For a quasi-compact quasi-separated 1-morphism of algebraic stacks, the
functors `R^i f_{QCoh,*}` are obtained by applying `Q` to the restriction of
the right-derived fppf module pushforward, lifted into étale `LQCoh^{fbc}`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `qCohHigherDirectImageFunctor`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The zero sheaf of modules is quasi-coherent. -/
instance quasiCoherentModuleProperty.containsZero (X : GroupoidsOver S) :
    (quasiCoherentModuleProperty X).ContainsZero :=
  sorry

/-- Quasi-coherent modules are closed under kernels. -/
instance quasiCoherentModuleProperty.isClosedUnderKernels (X : GroupoidsOver S) :
    (quasiCoherentModuleProperty X).IsClosedUnderKernels :=
  sorry

/-- Quasi-coherent modules are closed under cokernels. -/
instance quasiCoherentModuleProperty.isClosedUnderCokernels (X : GroupoidsOver S) :
    (quasiCoherentModuleProperty X).IsClosedUnderCokernels :=
  sorry

/-- Quasi-coherent modules are closed under finite products. -/
instance quasiCoherentModuleProperty.isClosedUnderFiniteProducts (X : GroupoidsOver S) :
    (quasiCoherentModuleProperty X).IsClosedUnderFiniteProducts :=
  sorry

/-- Quasi-coherent modules on an algebraic stack form an abelian category. -/
instance QCoh.instAbelian (X : GroupoidsOver S) [AlgebraicStack X] :
    Abelian (QCoh X) :=
  inferInstanceAs (Abelian (quasiCoherentModuleProperty X).FullSubcategory)

/-- Fppf modules on a category fibred in groupoids admit injective resolutions. -/
instance instHasInjectiveResolutions_fppfModules (X : GroupoidsOver S) :
    HasInjectiveResolutions (fppfModules X) :=
  sorry

/-- Restriction of `R^i f_*` of a quasi-coherent module lies in étale
`LQCoh^{fbc}`. -/
theorem qCohHigherDirectImage_mem_lqcohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X) :
    lqcohFbc Y
      ((QCoh.inclusion X ⋙
          (AlgebraicStack.modulePushforward f).rightDerived i ⋙
          restriction Y).obj F) :=
  sorry

/-- The degree-`i` quasi-coherent higher direct image functor
`R^i f_{QCoh,*} : QCoh 𝒳 ⥤ QCoh 𝒴`, obtained by lifting the restriction of
`(AlgebraicStack.modulePushforward f).rightDerived i` into `LQCoh^{fbc} 𝒴`
and applying `LQCohFbc.toQCoh`. -/
def qCohHigherDirectImageFunctor {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh X ⥤ QCoh Y :=
  (lqcohFbc Y).lift
      (QCoh.inclusion X ⋙
        (AlgebraicStack.modulePushforward f).rightDerived i ⋙ restriction Y)
      (qCohHigherDirectImage_mem_lqcohFbc f i) ⋙
    LQCohFbc.toQCoh Y

/-- `qCohHigherDirectImageFunctor` is the lift of restricted derived module
pushforward, followed by `Q`. -/
theorem qCohHigherDirectImageFunctor_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    qCohHigherDirectImageFunctor f i =
      (lqcohFbc Y).lift
          (QCoh.inclusion X ⋙
            (AlgebraicStack.modulePushforward f).rightDerived i ⋙ restriction Y)
          (qCohHigherDirectImage_mem_lqcohFbc f i) ⋙
        LQCohFbc.toQCoh Y :=
  rfl

/-- The degree-`i` quasi-coherent higher direct image `R^i f_{QCoh,*} F`. -/
def qCohHigherDirectImage {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : QCoh X) (i : ℕ) : QCoh Y :=
  (qCohHigherDirectImageFunctor f i).obj F

/-- `qCohHigherDirectImage f F i` is the object map of
`qCohHigherDirectImageFunctor f i`. -/
theorem qCohHigherDirectImage_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : QCoh X) (i : ℕ) :
    qCohHigherDirectImage f F i = (qCohHigherDirectImageFunctor f i).obj F :=
  rfl

end AlgebraicGeometry.GroupoidsOver
