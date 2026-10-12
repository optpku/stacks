/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Proposition_103_11_1_DirectImage

/-!
# Evaluation of quasi-coherent and étale direct images on flat objects

For a quasi-compact quasi-separated morphism of algebraic stacks, the étale
(higher) direct image of a quasi-coherent sheaf agrees with the quasi-coherent
(higher) direct image after evaluation at a flat object.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids Functor.Fiber Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The value of an étale `𝒪`-module at an object of the underlying category
fibred in groupoids. -/
abbrev etaleModuleObj {X : GroupoidsOver S} (F : etaleModules X) (x : X.total) :=
  F.val.obj (op x)

/-- `etaleModuleObj F x` is the component `F.val.obj (op x)`. -/
theorem etaleModuleObj_eq {X : GroupoidsOver S} (F : etaleModules X)
    (x : X.total) :
    etaleModuleObj F x = F.val.obj (op x) :=
  rfl

namespace LQCohFbc

/-- The component at a fiber object `y` of the adjunction counit `Q(G) ⟶ G`,
as a morphism of étale module values. This is the comparison
`Γ(y, Q(G)) ⟶ Γ(y, G)`. -/
def toQCohCounitEval {Y : GroupoidsOver S} [AlgebraicStack Y] {V : Over S}
    (y : Y.p.Fiber V) (adj : QCoh.toLQCohFbc Y ⊣ toQCoh Y) (G : LQCohFbc Y) :=
  ((inclusion Y).map (adj.counit.app G)).val.app (op (fiberInclusion.obj y))

/-- `toQCohCounitEval` is the `y`-component of the included adjunction counit. -/
theorem toQCohCounitEval_eq {Y : GroupoidsOver S} [AlgebraicStack Y]
    {V : Over S} (y : Y.p.Fiber V) (adj : QCoh.toLQCohFbc Y ⊣ toQCoh Y)
    (G : LQCohFbc Y) :
    toQCohCounitEval y adj G =
      ((inclusion Y).map (adj.counit.app G)).val.app
        (op (fiberInclusion.obj y)) :=
  rfl

/-- The adjunction counit `Q(G) ⟶ G` evaluates to an isomorphism at every
flat object of an algebraic stack. -/
instance toQCohCounitEval_isIso {Y : GroupoidsOver S} [AlgebraicStack Y]
    {V : Over S} (y : Y.p.Fiber V)
    [AlgebraicStack.Flat (YonedaSlice.representative y)]
    (adj : QCoh.toLQCohFbc Y ⊣ toQCoh Y) (G : LQCohFbc Y) :
    IsIso (toQCohCounitEval y adj G) :=
  sorry

end LQCohFbc

namespace QCoh

/-- The comparison `Γ(y, f_{QCoh,*} F) ⟶ Γ(y, f_* F)` obtained by evaluating
the counit of `toLQCohFbc ⊣ toQCoh` on the étale direct image of `F`. -/
def directImageCounitEval {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {V : Over S} (y : Y.p.Fiber V) (F : QCoh X) :=
  LQCohFbc.toQCohCounitEval y (toLQCohFbc_isRightAdjoint_toQCoh Y).some
    ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj F))

/-- `directImageCounitEval f y F` is `toQCohCounitEval` of the étale direct
image of `F`. -/
theorem directImageCounitEval_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {V : Over S} (y : Y.p.Fiber V) (F : QCoh X) :
    directImageCounitEval f y F =
      LQCohFbc.toQCohCounitEval y (toLQCohFbc_isRightAdjoint_toQCoh Y).some
        ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj F)) :=
  rfl

/-- Lemma 103.11.2 (1): Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated
morphism of algebraic stacks. Let `y : V ⟶ 𝒴` in `Ob(𝒴)` with `y` a flat
morphism, and let `F` be in `QCoh(𝒪_𝒳)`. Then
`(f_* F)(y) = (f_{QCoh,*} F)(y)`, as `Γ(y, -)` of the étale direct image
`LQCohFbc.directImage f` and of `QCoh.directImage f`. The comparison is the
counit component `directImageCounitEval f y F`. -/
@[stacks 0GQQ]
instance directImageCounitEval_isIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {V : Over S} (y : Y.p.Fiber V)
    [AlgebraicStack.Flat (YonedaSlice.representative y)] (F : QCoh X) :
    IsIso (directImageCounitEval f y F) :=
  sorry

/-- The comparison `Γ(y, R^i f_{QCoh,*} F) ⟶ Γ(y, R^i f_* F)` obtained by
evaluating the counit of `toLQCohFbc ⊣ toQCoh` on the étale higher direct
image of `F`. -/
def higherDirectImageCounitEval {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {V : Over S} (y : Y.p.Fiber V) (F : QCoh X) (i : ℕ) :=
  LQCohFbc.toQCohCounitEval y (toLQCohFbc_isRightAdjoint_toQCoh Y).some
    ((LQCohFbc.higherDirectImageFunctor f i).obj ((toLQCohFbc X).obj F))

/-- `higherDirectImageCounitEval f y F i` is `toQCohCounitEval` of the étale
higher direct image of `F`. -/
theorem higherDirectImageCounitEval_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {V : Over S} (y : Y.p.Fiber V) (F : QCoh X) (i : ℕ) :
    higherDirectImageCounitEval f y F i =
      LQCohFbc.toQCohCounitEval y (toLQCohFbc_isRightAdjoint_toQCoh Y).some
        ((LQCohFbc.higherDirectImageFunctor f i).obj ((toLQCohFbc X).obj F)) :=
  rfl

/-- Lemma 103.11.2 (2): Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated
morphism of algebraic stacks. Let `y : V ⟶ 𝒴` in `Ob(𝒴)` with `y` a flat
morphism, and let `F` be in `QCoh(𝒪_𝒳)`. Then
`(R^i f_* F)(y) = (R^i f_{QCoh,*} F)(y)` for `i : ℕ`, as `Γ(y, -)` of
`LQCohFbc.higherDirectImageFunctor f i` and of
`QCoh.higherDirectImageFunctor f i`. The comparison is the counit component
`higherDirectImageCounitEval f y F i`. Source `i ∈ ℤ` uses the convention
that negative derived images vanish. -/
@[stacks 0GQQ]
instance higherDirectImageCounitEval_isIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    {V : Over S} (y : Y.p.Fiber V)
    [AlgebraicStack.Flat (YonedaSlice.representative y)] (F : QCoh X)
    (i : ℕ) :
    IsIso (higherDirectImageCounitEval f y F i) :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
