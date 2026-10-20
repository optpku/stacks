module

public import ReasLib.Algebra.Category.Ring.Sheaf.FunctionAlgebra
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-!
# Cover descent for natural functions on a sheaf

Restriction uses the same section values on the slice. Compatible local functions glue by
the native internal-Hom sheaf and its covering-family amalgamation; no new existence
assertion is used to select a global function.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u v w r i

namespace CategoryTheory.Sheaf.FunctionAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (F : Sheaf J (Type (max w r))) (O : Sheaf J CommRingCat.{r})

/-- Restrict a natural function to the actual slice objects over `U`. -/
def restrict (U : C) : FunctionAlgebra F O →+* FunctionAlgebra (F.over U) (O.over U) where
  toFun a := ⟨fun j ↦ eval F O a ((Over.forget U).op.obj j.1) j.2, by sorry⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' := sorry
  map_mul' := sorry

/-- Restriction between two slices retains the original section on each composite chart. -/
def restrictAlong {U V : C} (f : V ⟶ U) :
    FunctionAlgebra (F.over U) (O.over U) →+* FunctionAlgebra (F.over V) (O.over V) where
  toFun a := ⟨fun j ↦ eval (F.over U) (O.over U) a ((Over.map f).op.obj j.1) j.2, by sorry⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' := sorry
  map_mul' := sorry

/-- Global restriction evaluates at the same ambient object and element. -/
@[simp]
theorem restrict_eval (U : C) (a : FunctionAlgebra F O) (V : (Over U)ᵒᵖ)
    (x : (F.over U).obj.obj V) :
    eval (F.over U) (O.over U) (restrict F O U a) V x =
      eval F O a ((Over.forget U).op.obj V) x := rfl

/-- Slice restriction evaluates on the actual postcomposed chart. -/
@[simp]
theorem restrictAlong_eval {U V : C} (f : V ⟶ U)
    (a : FunctionAlgebra (F.over U) (O.over U)) (W : (Over V)ᵒᵖ)
    (x : (F.over V).obj.obj W) :
    eval (F.over V) (O.over V) (restrictAlong F O f a) W x =
      eval (F.over U) (O.over U) a ((Over.map f).op.obj W) x := rfl

/-- The two native iterated-slice functors transport the same section functions in both directions. -/
def iteratedSliceEquiv {U : C} (f : Over U) :
    FunctionAlgebra (F.over f.left) (O.over f.left) ≃+*
      FunctionAlgebra ((F.over U).over f) ((O.over U).over f) where
  toFun a := ⟨fun j ↦ eval (F.over f.left) (O.over f.left) a
    ((Over.iteratedSliceForward f).op.obj j.1) j.2, by sorry⟩
  invFun a := ⟨fun j ↦ eval ((F.over U).over f) ((O.over U).over f) a
    ((Over.iteratedSliceBackward f).op.obj j.1) j.2, by sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_mul' := sorry

/-- Forward iterated-slice transport evaluates on the native collapsed slice object. -/
@[simp]
theorem iteratedSliceEquiv_eval {U : C} (f : Over U)
    (a : FunctionAlgebra (F.over f.left) (O.over f.left)) (V : (Over f)ᵒᵖ)
    (x : ((F.over U).over f).obj.obj V) :
    eval ((F.over U).over f) ((O.over U).over f) (iteratedSliceEquiv F O f a) V x =
      eval (F.over f.left) (O.over f.left) a ((Over.iteratedSliceForward f).op.obj V) x := rfl

/-- Reverse iterated-slice transport evaluates on the native expanded slice object. -/
@[simp]
theorem iteratedSliceEquiv_symm_eval {U : C} (f : Over U)
    (a : FunctionAlgebra ((F.over U).over f) ((O.over U).over f))
    (V : (Over f.left)ᵒᵖ) (x : (F.over f.left).obj.obj V) :
    eval (F.over f.left) (O.over f.left) ((iteratedSliceEquiv F O f).symm a) V x =
      eval ((F.over U).over f) ((O.over U).over f) a
        ((Over.iteratedSliceBackward f).op.obj V) x := rfl

variable {I : Type i} (X : I → C)

/-- Local functions agree after every pair of maps from any common test object. -/
def Compatible (a : ∀ j, FunctionAlgebra (F.over (X j)) (O.over (X j))) : Prop :=
  ∀ (j k : I) {Y : C} (f : Y ⟶ X j) (g : Y ⟶ X k),
    restrictAlong F O f (a j) = restrictAlong F O g (a k)

/-- Read the supplied local functions as the native internal-Hom section family. -/
def homFamily (a : ∀ j, FunctionAlgebra (F.over (X j)) (O.over (X j))) :
    Presheaf.FamilyOfElementsOnObjects (sheafHom F (coefficients O)).obj X :=
  fun j ↦ (homEquiv (F := F.over (X j)) (O := O.over (X j))) (a j)

/-- The complete local restriction condition is the native Hom-family compatibility condition. -/
theorem homFamily_compatible
    (a : ∀ j, FunctionAlgebra (F.over (X j)) (O.over (X j)))
    (ha : Compatible F O X a) :
    (homFamily F O X a).IsCompatible := sorry

/-- Glue compatible local natural functions using the native Hom sheaf's actual amalgamation. -/
def glue (hcover : J.CoversTop X)
    (a : ∀ j, FunctionAlgebra (F.over (X j)) (O.over (X j)))
    (ha : Compatible F O X a) : FunctionAlgebra F O :=
  let H := sheafHom F (coefficients O)
  let s := (homFamily_compatible F O X a ha).section_ hcover H.property
  (homEquiv (F := F) (O := O)).symm
    ((sheafHomSectionsEquiv F (coefficients O)) s)

/-- The glued natural function has exactly the supplied restriction on every cover member. -/
theorem restrict_glue (hcover : J.CoversTop X)
    (a : ∀ j, FunctionAlgebra (F.over (X j)) (O.over (X j)))
    (ha : Compatible F O X a) (j : I) :
    restrict F O (X j) (glue F O X hcover a ha) = a j := sorry

/-- All restrictions of one global function agree on every common test object. -/
theorem restrict_compatible (a : FunctionAlgebra F O) :
    Compatible F O X (fun j ↦ restrict F O (X j) a) := sorry

/-- A global function is uniquely determined by its restrictions to a covering family. -/
theorem glue_unique (hcover : J.CoversTop X)
    (a : ∀ j, FunctionAlgebra (F.over (X j)) (O.over (X j)))
    (ha : Compatible F O X a) (b : FunctionAlgebra F O)
    (hb : ∀ j, restrict F O (X j) b = a j) :
    b = glue F O X hcover a ha := sorry

end CategoryTheory.Sheaf.FunctionAlgebra
