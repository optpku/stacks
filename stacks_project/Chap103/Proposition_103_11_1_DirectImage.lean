module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import stacks_project.Chap103.Lemma_103_6_2
public import stacks_project.Chap103.Lemma_103_10_1

/-!
# Quasi-coherent direct images along quasi-compact quasi-separated morphisms

The functors `f_*` and `R^i f_*` on `LQCoh^{fbc}`, and the quasi-coherent
direct image `f_{QCoh,*}` obtained by composing with `QCoh.toLQCohFbc` and
`LQCohFbc.toQCoh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace LQCohFbc

/-- Étale direct image along a quasi-compact quasi-separated morphism of
algebraic stacks sends `LQCoh^{fbc}` to `LQCoh^{fbc}`. -/
theorem mem_directImage {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : LQCohFbc X) :
    lqcohFbc Y ((moduleDirectImage f).obj ((inclusion X).obj F)) :=
  sorry

/-- Direct image `f_* : LQCoh^{fbc}(𝒪_𝒳) ⥤ LQCoh^{fbc}(𝒪_𝒴)` along a
quasi-compact quasi-separated morphism of algebraic stacks. -/
def directImage {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    LQCohFbc X ⥤ LQCohFbc Y :=
  (lqcohFbc Y).lift (inclusion X ⋙ moduleDirectImage f) (mem_directImage f)

/-- The underlying étale functor of `LQCohFbc.directImage f` is
`moduleDirectImage f`. -/
theorem directImage_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    directImage f ⋙ inclusion Y = inclusion X ⋙ moduleDirectImage f :=
  rfl

/-- Direct image on `LQCoh^{fbc}` is additive. -/
instance directImage_additive {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (directImage f).Additive :=
  sorry

/-- Étale higher direct image along a quasi-compact quasi-separated morphism of
algebraic stacks sends `LQCoh^{fbc}` to `LQCoh^{fbc}`. -/
theorem mem_higherDirectImage {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : LQCohFbc X) :
    lqcohFbc Y ((moduleHigherDirectImageFunctor f i).obj ((inclusion X).obj F)) :=
  sorry

/-- Higher direct image `R^i f_* : LQCoh^{fbc}(𝒪_𝒳) ⥤ LQCoh^{fbc}(𝒪_𝒴)`. -/
def higherDirectImageFunctor {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    LQCohFbc X ⥤ LQCohFbc Y :=
  (lqcohFbc Y).lift (inclusion X ⋙ moduleHigherDirectImageFunctor f i)
    (mem_higherDirectImage f i)

/-- The underlying étale functor of `LQCohFbc.higherDirectImageFunctor f i` is
`moduleHigherDirectImageFunctor f i`. -/
theorem higherDirectImageFunctor_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    higherDirectImageFunctor f i ⋙ inclusion Y =
      inclusion X ⋙ moduleHigherDirectImageFunctor f i :=
  rfl

/-- Higher direct image on `LQCoh^{fbc}` is additive. -/
instance higherDirectImageFunctor_additive {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    (higherDirectImageFunctor f i).Additive :=
  sorry

end LQCohFbc

namespace QCoh

/-- The quasi-coherent direct image `f_{QCoh,*}` is the composition
`toLQCohFbc ⋙ LQCohFbc.directImage f ⋙ LQCohFbc.toQCoh`. -/
def directImage {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    QCoh X ⥤ QCoh Y :=
  toLQCohFbc X ⋙ LQCohFbc.directImage f ⋙ LQCohFbc.toQCoh Y

/-- `QCoh.directImage f` is `toLQCohFbc` followed by étale `f_*` on `LQCoh^{fbc}`
and `Q`. -/
theorem directImage_eq {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    directImage f = toLQCohFbc X ⋙ LQCohFbc.directImage f ⋙ LQCohFbc.toQCoh Y :=
  rfl

/-- Quasi-coherent direct image is additive. -/
instance directImage_additive {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] :
    (directImage f).Additive :=
  sorry

/-- The degree-`i` quasi-coherent higher direct image functor `R^i f_{QCoh,*}`. -/
def higherDirectImageFunctor {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    QCoh X ⥤ QCoh Y :=
  toLQCohFbc X ⋙ LQCohFbc.higherDirectImageFunctor f i ⋙ LQCohFbc.toQCoh Y

/-- `QCoh.higherDirectImageFunctor f i` is `toLQCohFbc` followed by étale
`R^i f_*` on `LQCoh^{fbc}` and `Q`. -/
theorem higherDirectImageFunctor_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    higherDirectImageFunctor f i =
      toLQCohFbc X ⋙ LQCohFbc.higherDirectImageFunctor f i ⋙ LQCohFbc.toQCoh Y :=
  rfl

/-- Quasi-coherent higher direct image functors are additive. -/
instance higherDirectImageFunctor_additive {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ) :
    (higherDirectImageFunctor f i).Additive :=
  sorry

/-- The degree-`i` quasi-coherent higher direct image `R^i f_{QCoh,*} F`. -/
def higherDirectImage {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : QCoh X) (i : ℕ) : QCoh Y :=
  (higherDirectImageFunctor f i).obj F

/-- `QCoh.higherDirectImage f F i` is the object map of
`QCoh.higherDirectImageFunctor f i`. -/
theorem higherDirectImage_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : QCoh X) (i : ℕ) :
    higherDirectImage f F i = (higherDirectImageFunctor f i).obj F :=
  rfl

end QCoh

end AlgebraicGeometry.GroupoidsOver
