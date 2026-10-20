module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.InDimensions
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# The flat-in-dimensions functor

This module defines the subterminal functor recording the base changes on which a finite-type
quasicoherent module is flat over the base in dimensions at least a fixed natural number.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (n : ℕ)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/-- Flatness in dimensions at least `n` is preserved when the base scheme is changed further. -/
theorem flatInDimensionsGE_pullback {T T' : Over S} (g : T' ⟶ T)
    (h : Modules.flatOverInDimensionsGE
      (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n) :
    Modules.flatOverInDimensionsGE
      (Modules.baseChangeModule f T'.hom ℱ) (pullback.snd f T'.hom) n := sorry

/-- The subfunctor of the terminal `PUnit` functor cut out by flatness of the base-changed module
in dimensions at least `n`. -/
def flatInDimensionsSubfunctor :
    CategoryTheory.Subfunctor
      ((Functor.const (Over S)ᵒᵖ).obj (PUnit : Type u)) where
  obj T := fun _ ↦ Modules.flatOverInDimensionsGE
    (Modules.baseChangeModule f T.unop.hom ℱ) (pullback.snd f T.unop.hom) n
  map g _ h := flatInDimensionsGE_pullback f ℱ n g.unop h

/-- Membership of the terminal section is exactly flatness of the base-changed module in
dimensions at least `n`. -/
theorem mem_flatInDimensionsSubfunctor (T : Over S) :
    PUnit.unit ∈ (flatInDimensionsSubfunctor f ℱ n).obj (op T) ↔
      Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n := sorry

/-- The subterminal contravariant functor recording flatness of the base-changed module in
dimensions at least `n`. -/
def flatInDimensionsFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (flatInDimensionsSubfunctor f ℱ n).toFunctor

/-- The value of the flat-in-dimensions functor is inhabited exactly when the base-changed
module is flat over the base in dimensions at least `n`. -/
theorem flatInDimensionsFunctor_nonempty_iff (T : Over S) :
    Nonempty ((flatInDimensionsFunctor f ℱ n).obj (op T)) ↔
      Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n := sorry

/-- The value of the flat-in-dimensions functor is empty exactly when the base-changed module
is not flat over the base in dimensions at least `n`. -/
theorem flatInDimensionsFunctor_isEmpty_iff (T : Over S) :
    IsEmpty ((flatInDimensionsFunctor f ℱ n).obj (op T)) ↔
      ¬ Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) n := sorry

/-- Every value of the flat-in-dimensions functor has at most one element. -/
theorem flatInDimensionsFunctor_obj_subsingleton (T : Over S) :
    Subsingleton ((flatInDimensionsFunctor f ℱ n).obj (op T)) := sorry

end AlgebraicGeometry.Scheme.Flattening
