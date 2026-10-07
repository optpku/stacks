module

public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Definition
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of Delta Functors

The constructors here compose a delta functor with a target-side exact
triangulated functor or a source-side exact functor between abelian categories.
-/

@[expose] public section

namespace CategoryTheory.DeltaFunctor

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe vA vA' vD vD' uA uA' uD uD'

section Postcompose

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type uD'} [Category.{vD'} D'] [HasZeroObject D'] [HasShift D' ℤ]
variable [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

variable (G : DeltaFunctor A D) (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/-- Postcomposition with an exact triangulated functor turns a `DeltaFunctor A D`
into a `DeltaFunctor A D'`. -/
@[stacks 0151]
noncomputable def postcomposeExactFunctor : DeltaFunctor A D' where
  toFunctor := G.toFunctor ⋙ F
  additive :=
    ⟨fun {X Y} {f g : X ⟶ Y} ↦ by
      change F.map (G.map (f + g)) = F.map (G.map f) + F.map (G.map g)
      rw [G.additive.map_add]
      exact (AdditiveFunctor.of F).property.map_add⟩
  δ := fun {S} hS ↦ F.map (G.δ hS) ≫ (F.commShiftIso (1 : ℤ)).hom.app (G.obj S.X₁)
  map_distinguished := fun {S} hS ↦ by
    change Triangle.mk
      (F.map (G.triangle hS).mor₁)
      (F.map (G.triangle hS).mor₂)
      (F.map (G.triangle hS).mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app (G.triangle hS).obj₁) ∈
        distTriang D'
    exact F.map_distinguished (G.triangle hS) (G.triangle_distinguished hS)
  δ_naturality := fun {S T} hS hT φ ↦ by
    change CommSq
      (F.map (G.map φ.τ₃))
      (F.map (G.δ hS) ≫ (F.commShiftIso (1 : ℤ)).hom.app (G.obj S.X₁))
      (F.map (G.δ hT) ≫ (F.commShiftIso (1 : ℤ)).hom.app (G.obj T.X₁))
      ((shiftFunctor D' 1).map (F.map (G.map φ.τ₁)))
    exact CommSq.vert_comp
      ((G.δ_naturality hS hT φ).map F)
      (CommSq.mk (F.commShiftIso_hom_naturality (G.map φ.τ₁) (1 : ℤ)))

namespace postcomposeExactFunctor

/-- Postcomposition sends a connecting morphism through the exact functor and
then through its comparison with shift. -/
@[simp, stacks 0151 "connecting map after exact postcomposition"]
theorem δ {S : ShortComplex A} (hS : S.ShortExact) :
    (G.postcomposeExactFunctor F).δ hS =
      F.map (G.δ hS) ≫
        (F.commShiftIso (1 : ℤ)).hom.app (G.obj S.X₁) := sorry

end postcomposeExactFunctor

/-- The underlying functor of `postcomposeExactFunctor` is ordinary functor composition. -/
@[simp]
theorem postcomposeExactFunctor_toFunctor :
    (G.postcomposeExactFunctor F).toFunctor = G.toFunctor ⋙ F := rfl

end Postcompose

section Precompose

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (G : DeltaFunctor A D) (H : A' ⥤ₑ A)

/-- Precomposition with an exact functor between abelian categories turns a
`DeltaFunctor A D` into a `DeltaFunctor A' D`. -/
@[stacks 0151]
noncomputable def precomposeExactFunctor : DeltaFunctor A' D where
  toFunctor := ((AdditiveFunctor.ofExact A' A).obj H).obj ⋙ G.toFunctor
  additive :=
    ⟨fun {X Y} {f g : X ⟶ Y} ↦ by
      let H' := (AdditiveFunctor.ofExact A' A).obj H
      change G.map (H'.obj.map (f + g)) = G.map (H'.obj.map f) + G.map (H'.obj.map g)
      have hH : H'.obj.map (f + g) = H'.obj.map f + H'.obj.map g :=
        H'.property.map_add
      rw [hH]
      exact G.additive.map_add⟩
  δ := fun {_} hS ↦ G.δ (hS.map_of_exact H.obj)
  map_distinguished := fun {_} hS ↦ by
    change G.triangle (hS.map_of_exact H.obj) ∈ distTriang D
    exact G.triangle_distinguished (hS.map_of_exact H.obj)
  δ_naturality := fun {_ _} hS hT φ ↦ by
    change CommSq
      (G.map (H.obj.map φ.τ₃))
      (G.δ (hS.map_of_exact H.obj))
      (G.δ (hT.map_of_exact H.obj))
      ((shiftFunctor D 1).map (G.map (H.obj.map φ.τ₁)))
    exact G.δ_naturality (hS.map_of_exact H.obj) (hT.map_of_exact H.obj)
      ((H.obj.mapShortComplex).map φ)

namespace precomposeExactFunctor

/-- Precomposition evaluates the original connecting morphism on the image
short exact sequence. -/
@[simp, stacks 0151 "connecting map after exact precomposition"]
theorem δ {S : ShortComplex A'} (hS : S.ShortExact) :
    (G.precomposeExactFunctor H).δ hS =
      G.δ (hS.map_of_exact H.obj) := sorry

end precomposeExactFunctor

/-- The underlying functor of `precomposeExactFunctor` is ordinary functor composition. -/
@[simp]
theorem precomposeExactFunctor_toFunctor :
    (G.precomposeExactFunctor H).toFunctor = H.obj ⋙ G.toFunctor := rfl

end Precompose

end CategoryTheory.DeltaFunctor
