/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral tensor powers of invertible module sheaves

The canonical owner is the integer power of the tensor-right autoequivalence, evaluated at the
structure module. The monoidal structure is inferred from the ringed-site tensor owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace InvertiblePower

/-- The degree-`n` tensor power of an invertible module sheaf is the image of the structure
module under the `n`th power of its tensor-right autoequivalence. -/
@[stacks 01CU]
noncomputable abbrev sheaf
    (L : Modules X) [isInvertibleObject L] (n : ℤ) : Modules X :=
  MonoidalCategory.InvertiblePower.eval L
    (SheafOfModules.unit X.ringCatSheaf : Modules X) n

/-- The autoequivalence expression defining an integral tensor power. -/
theorem sheaf_def
    (L : Modules X) [isInvertibleObject L] (n : ℤ) :
    sheaf L n =
      (((tensorRight L).asEquivalence ^ n).functor.obj
        (SheafOfModules.unit X.ringCatSheaf : Modules X)) := sorry

/-- The textbook tensor power based at the structure module agrees with the categorical tensor
power based at the monoidal unit. This bridge is induced by the canonical comparison between those
two unit models. -/
@[stacks 01CU "structure-module/categorical tensor-power comparison"]
noncomputable def categoricalIso
    (L : Modules X) [isInvertibleObject L] (n : ℤ) :
    sheaf L n ≅ MonoidalCategory.InvertiblePower.obj L n :=
  MonoidalCategory.InvertiblePower.evalMapIso L
    (AlgebraicGeometry.RingedSpace.unitIsoTensorUnit X) n

/-- Transport integral tensor powers along an equality of their degrees. -/
noncomputable def indexIso
    (L : Modules X) [isInvertibleObject L] {m n : ℤ} (h : m = n) :
    sheaf L m ≅ sheaf L n :=
  MonoidalCategory.InvertiblePower.evalIndexIso L
    (SheafOfModules.unit X.ringCatSheaf : Modules X) h

end InvertiblePower

/- Textbook notation for integral tensor powers of invertible module sheaves. -/
scoped[AlgebraicGeometry] infixr:80 " ^⊗ " =>
  AlgebraicGeometry.RingedSpace.InvertiblePower.sheaf

end AlgebraicGeometry.RingedSpace

