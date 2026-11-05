module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Homology.HomotopyCategory.Lift
public import ReasLib.Algebra.Homology.HomotopyCategory.TotalFunctor
public import ReasLib.Algebra.Homology.HomotopyCategory.TotalFunctor.Triangulated
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-factor derived tensor functors

This leaf separates the concrete homotopy-level tensor construction from the
additional existence theorem needed to left derive it.  The construction works
in every monoidal abelian category in which cochain tensor totalization is
available; a `DerivedTensor.Has` instance records only the non-formal
derivability input.
@stack 064M
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe v u w

namespace CategoryTheory.DerivedCategory

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ (K L : CochainComplex C ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]

/-- Totalized tensoring with a fixed right cochain complex. -/
noncomputable abbrev DerivedTensor.Right.complexFunctor
    (P : CochainComplex C ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  ((curriedTensor C).map₂CochainComplex).flip.obj P

/-- Fixed-right-factor tensoring by a cochain complex, descended through the reusable homotopy
lift and then sent to the derived category. -/
noncomputable abbrev DerivedTensor.Right.sourceFunctorOfComplex
    (P : CochainComplex C ℤ) :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  Functor.Homotopy.BifunctorTotal.rightFixed (curriedTensor C) P ⋙
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)

/-- Fixed-right-factor tensoring on the homotopy category, using the canonical chosen complex
representative of a derived object. -/
noncomputable abbrev DerivedTensor.Right.sourceFunctor
    (E : DerivedCategory C) :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  DerivedTensor.Right.sourceFunctorOfComplex
    ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E)

/-- Totalized tensoring with a fixed left cochain complex. -/
noncomputable abbrev DerivedTensor.Left.complexFunctor
    (P : CochainComplex C ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  ((curriedTensor C).map₂CochainComplex).obj P

/-- Fixed-left-factor tensoring by a cochain complex, descended through the reusable homotopy
lift and then sent to the derived category. -/
noncomputable abbrev DerivedTensor.Left.sourceFunctorOfComplex
    (P : CochainComplex C ℤ) :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  Functor.Homotopy.BifunctorTotal.leftFixed (curriedTensor C) P ⋙
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)

/-- Fixed-left-factor tensoring on the homotopy category, using the canonical chosen complex
representative of a derived object. -/
noncomputable abbrev DerivedTensor.Left.sourceFunctor
    (E : DerivedCategory C) :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  DerivedTensor.Left.sourceFunctorOfComplex
    ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E)

/-- A monoidal abelian category supports unbounded fixed-right derived tensoring when the
left-derived value of `DerivedTensor.Right.sourceFunctor E` exists at every object. -/
class DerivedTensor.Right.Has : Prop where
  /-- The fixed-right-factor homotopy tensor functor is pointwise left derivable everywhere. -/
  everywhereDefined (E : DerivedCategory C) :
    Functor.LeftDerived.EverywhereDefined (DerivedTensor.Right.sourceFunctor E)
      (HomotopyCategory.quasiIso C (up ℤ))

attribute [instance] DerivedTensor.Right.Has.everywhereDefined

/-- A monoidal abelian category supports unbounded fixed-left derived tensoring when the
left-derived value of `DerivedTensor.Left.sourceFunctor E` exists at every object. -/
class DerivedTensor.Left.Has : Prop where
  /-- The fixed-left-factor homotopy tensor functor is pointwise left derivable everywhere. -/
  everywhereDefined (E : DerivedCategory C) :
    Functor.LeftDerived.EverywhereDefined (DerivedTensor.Left.sourceFunctor E)
      (HomotopyCategory.quasiIso C (up ℤ))

attribute [instance] DerivedTensor.Left.Has.everywhereDefined

/-- A bidirectional derived tensor model packages the independent fixed-right and fixed-left
derivability inputs. Individual constructions ask only for the direction they use. -/
class DerivedTensor.Has : Prop where
  /-- Fixed-right derived tensoring is available. -/
  right : DerivedTensor.Right.Has (C := C)
  /-- Fixed-left derived tensoring is available. -/
  left : DerivedTensor.Left.Has (C := C)

attribute [instance] DerivedTensor.Has.right DerivedTensor.Has.left

/-- Derived tensoring on the left by a variable object and on the right by the fixed derived
object `E`. -/
@[stacks 064M "fixed-right derived tensor functor"]
noncomputable abbrev DerivedTensor.Right.functor
    (E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
    DerivedCategory C ⥤ DerivedCategory C :=
  (DerivedTensor.Right.sourceFunctor E).totalLeftDerived
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C (up ℤ))

/-- The derived tensor object with variable left factor `K` and fixed right factor `E`. -/
@[stacks 064M "fixed-right derived tensor object"]
noncomputable abbrev DerivedTensor.Right.obj
    (K E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
    DerivedCategory C :=
  (DerivedTensor.Right.functor E).obj K

namespace DerivedTensor

/-- Scoped notation for the fixed-right derived tensor object. -/
scoped infixr:70 " ⊗ᴸ " => Right.obj

end DerivedTensor

/-- Derived tensoring on the right by a variable object and on the left by the fixed derived
object `E`. -/
@[stacks 064M "fixed-left derived tensor functor"]
noncomputable abbrev DerivedTensor.Left.functor
    (E : DerivedCategory C) [DerivedTensor.Left.Has (C := C)] :
    DerivedCategory C ⥤ DerivedCategory C :=
  (DerivedTensor.Left.sourceFunctor E).totalLeftDerived
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C (up ℤ))

/-- The derived tensor object with fixed left factor `E` and variable right factor `K`. -/
@[stacks 064M "fixed-left derived tensor object"]
noncomputable abbrev DerivedTensor.Left.obj
    (E K : DerivedCategory C) [DerivedTensor.Left.Has (C := C)] :
    DerivedCategory C :=
  (DerivedTensor.Left.functor E).obj K

/-- The canonical counit presenting `DerivedTensor.Right.functor E` as the total left derived
functor of fixed-right tensoring on the homotopy category. -/
noncomputable abbrev DerivedTensor.Right.counit
    (E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) ⋙
      DerivedTensor.Right.functor E ⟶ DerivedTensor.Right.sourceFunctor E :=
  (DerivedTensor.Right.sourceFunctor E).totalLeftDerivedCounit
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C (up ℤ))

/-- The canonical counit presenting `DerivedTensor.Left.functor E` as the total left derived
functor of fixed-left tensoring on the homotopy category. -/
noncomputable abbrev DerivedTensor.Left.counit
    (E : DerivedCategory C) [DerivedTensor.Left.Has (C := C)] :
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) ⋙
      DerivedTensor.Left.functor E ⟶ DerivedTensor.Left.sourceFunctor E :=
  (DerivedTensor.Left.sourceFunctor E).totalLeftDerivedCounit
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C (up ℤ))

/-- The canonical total fixed-right derived tensor functor commutes with shifts. -/
noncomputable instance DerivedTensor.Right.commShift
    (E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
    (DerivedTensor.Right.functor E).CommShift ℤ :=
  Functor.totalLeftDerived_commShift (DerivedTensor.Right.sourceFunctor E)
    (HomotopyCategory.quasiIso C (up ℤ)) DerivedCategory.Qh

/-- The canonical total fixed-left derived tensor functor commutes with shifts. -/
noncomputable instance DerivedTensor.Left.commShift
    (E : DerivedCategory C) [DerivedTensor.Left.Has (C := C)] :
    (DerivedTensor.Left.functor E).CommShift ℤ :=
  Functor.totalLeftDerived_commShift (DerivedTensor.Left.sourceFunctor E)
    (HomotopyCategory.quasiIso C (up ℤ)) DerivedCategory.Qh

end


end CategoryTheory.DerivedCategory
