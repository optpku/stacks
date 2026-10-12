/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Composition.Naturality
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality in the Target Exact Functor

A shift-compatible natural transformation between exact triangulated target
functors induces a morphism between the corresponding postcomposed delta
functors.
-/

open CategoryTheory.Pretriangulated

noncomputable section

universe vA vD vD' uA uD uD'

namespace CategoryTheory.DeltaFunctor.postcomposeExactFunctor.target

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {D : Type uD} [Category.{vD} D] [Limits.HasZeroObject D]
  [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type uD'} [Category.{vD'} D'] [Limits.HasZeroObject D']
  [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable (G : DeltaFunctor A D)

/-- A shift-compatible target transformation preserves the connecting maps
of exact postcomposition. -/
@[stacks 0151 "target naturality of exact postcomposition"]
theorem map_comm {F F' : D ⥤ D'}
    [F.CommShift ℤ] [F.IsTriangulated]
    [F'.CommShift ℤ] [F'.IsTriangulated]
    (τ : F ⟶ F') [NatTrans.CommShift τ ℤ]
    {S : ShortComplex A} (hS : S.ShortExact) :
    CommSq ((Functor.whiskerLeft G.toFunctor τ).app S.X₃)
      ((G.postcomposeExactFunctor F).δ hS)
      ((G.postcomposeExactFunctor F').δ hS)
      (((Functor.whiskerLeft G.toFunctor τ).app S.X₁)⟦(1 : ℤ)⟧') := sorry

/-- A shift-compatible transformation of exact target functors induces a
morphism of postcomposed delta functors. -/
@[stacks 0151 "map of exact postcomposition in the target functor"]
noncomputable def map {F F' : D ⥤ D'}
    [F.CommShift ℤ] [F.IsTriangulated]
    [F'.CommShift ℤ] [F'.IsTriangulated]
    (τ : F ⟶ F') [NatTrans.CommShift τ ℤ] :
    G.postcomposeExactFunctor F ⟶ G.postcomposeExactFunctor F' where
  app := Functor.whiskerLeft G.toFunctor τ
  comm := fun {_} hS ↦ map_comm G τ hS

/-- The underlying component of target naturality is evaluated at the value
of the original delta functor. -/
@[simp]
theorem map_app {F F' : D ⥤ D'}
    [F.CommShift ℤ] [F.IsTriangulated]
    [F'.CommShift ℤ] [F'.IsTriangulated]
    (τ : F ⟶ F') [NatTrans.CommShift τ ℤ] (X : A) :
    (map G τ).app.app X = τ.app (G.obj X) := sorry

/-- Target naturality preserves identity transformations. -/
@[simp]
theorem map_id (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] :
    map G (𝟙 F) = 𝟙 (G.postcomposeExactFunctor F) := sorry

/-- Target naturality preserves composition of shift-compatible
transformations. -/
@[simp]
theorem map_comp {F F' F'' : D ⥤ D'}
    [F.CommShift ℤ] [F.IsTriangulated]
    [F'.CommShift ℤ] [F'.IsTriangulated]
    [F''.CommShift ℤ] [F''.IsTriangulated]
    (τ : F ⟶ F') [NatTrans.CommShift τ ℤ]
    (σ : F' ⟶ F'') [NatTrans.CommShift σ ℤ] :
    map G (τ ≫ σ) = map G τ ≫ map G σ := sorry

end CategoryTheory.DeltaFunctor.postcomposeExactFunctor.target
