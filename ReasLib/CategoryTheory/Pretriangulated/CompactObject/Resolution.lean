module

public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Approximation
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Resolutions by Compact Generators

@stack 09SN

This leaf packages the sequential resolution supplied by a compact generating
family.  It separates the concrete resolution data from its existence theorem,
so consumers can use stage, triangle, and homotopy-colimit information without
unpacking a long existential statement.
-/

open CategoryTheory
open CategoryTheory.Category
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe w v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{max u v w} D]
variable {I : Type w}

/-- Stacks 09SN, Lemma 13.37.3: a sequential resolution of `A` by arbitrary direct sums of
shifts of a family `E`, together with its chosen homotopy-colimit identification. -/
@[stacks 09SN]
structure GeneratingFamilyResolution (E : I → D) (A : D) where
  /-- The objects in the sequential resolution. -/
  obj : ℕ → D
  /-- The successive transition morphisms in the resolution. -/
  map : ∀ n : ℕ, obj n ⟶ obj (n + 1)
  /-- The first vertices of the distinguished stage triangles. -/
  piece : ℕ → D
  /-- The first morphisms in the distinguished stage triangles. -/
  pieceToObj : ∀ n : ℕ, piece n ⟶ obj n
  /-- The connecting morphisms in the distinguished stage triangles. -/
  connecting : ∀ n : ℕ, obj (n + 1) ⟶ (piece n)⟦(1 : ℤ)⟧
  /-- The chosen sequential homotopy-colimit object. -/
  hocolim : D
  /-- Its identification with the target. -/
  iso : hocolim ≅ A
  /-- The initial object and triangle pieces are direct sums of shifts of `E`. -/
  approximation : IsGeneratingFamilyApproximation E obj map piece pieceToObj connecting
  /-- The chosen object is a homotopy colimit of the sequential resolution. -/
  isHomotopyColimit : HomotopyColimit.IsOf (Functor.ofSequence map) hocolim

namespace GeneratingFamilyResolution

variable {E : I → D} {A : D}

/-- The sequential diagram underlying a generating-family resolution. -/
@[stacks 09SN]
def sequence (R : GeneratingFamilyResolution E A) : ℕ ⥤ D :=
  Functor.ofSequence R.map

/-- The sequence of a generating-family resolution has the specified objects. -/
@[stacks 09SN, simp]
theorem sequence_obj (R : GeneratingFamilyResolution E A) (n : ℕ) :
    R.sequence.obj n = R.obj n := sorry

/-- The initial object of a compact-generator resolution is a direct sum of shifts of the
generators. -/
@[stacks 09SN]
theorem initial (R : GeneratingFamilyResolution E A) :
    ObjectProperty.directSumOfShifts E (R.obj 0) := sorry

/-- Each triangle piece of a compact-generator resolution is a direct sum of shifts of the
generators. -/
@[stacks 09SN]
theorem pieces (R : GeneratingFamilyResolution E A) (n : ℕ) :
    ObjectProperty.directSumOfShifts E (R.piece n) := sorry

/-- The triangle at every stage of a compact-generator resolution is distinguished. -/
@[stacks 09SN]
theorem triangleDistinguished (R : GeneratingFamilyResolution E A) (n : ℕ) :
    Triangle.mk (R.pieceToObj n) (R.map n) (R.connecting n) ∈ distTriang D := sorry

/-- The transition map of the underlying sequence at a successor stage is the chosen resolution
map. -/
@[stacks 09SN, simp]
theorem sequence_map_succ (R : GeneratingFamilyResolution E A) (n : ℕ) :
    R.sequence.map (homOfLE (n.le_add_right 1)) = R.map n := sorry

/-- The chosen homotopy-colimit object has the expected universal triangle presentation. -/
@[stacks 09SN]
theorem hocolim_isOf (R : GeneratingFamilyResolution E A) :
    HomotopyColimit.IsOf R.sequence R.hocolim := sorry

/-- Compact generators give a generating-family resolution of every target object. -/
@[stacks 09SN]
theorem nonempty (hcompact : ∀ i : I, IsCompactObject (E i))
    (hgenerate : IsGeneratingFamily E) (A : D) :
    Nonempty (GeneratingFamilyResolution E A) := sorry

end GeneratingFamilyResolution

end

end CategoryTheory
