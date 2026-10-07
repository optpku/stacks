module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Sites.Monoidal
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal closure of locally constant sheaves

This leaf first gives the closure API for sheaves valued in an arbitrary monoidal category, with
the monoidal structures and monoidal constant/restriction functors made explicit as typeclass
inputs. It then specializes to sheaves of modules over a commutative ring.

The module specialization imports the named ReasLib owner of the localization-induced monoidal
structure.  This avoids reconstructing that canonical instance locally at every use site.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory CategoryTheory.ObjectProperty

noncomputable section

universe u v w w'

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Constant

variable {D : Type w} [Category.{w'} D] [MonoidalCategory D]
variable [HasWeakSheafify J D]
variable [MonoidalCategory (Sheaf J D)]
variable [Functor.Monoidal (constantSheaf J D)]

namespace IsConstant

/-- Constant sheaves are closed under tensor products whenever the constant-sheaf functor is
monoidal. -/
theorem tensor {F G : Sheaf J D} [IsConstant J F] [IsConstant J G] :
    IsConstant J (F ⊗ G) := sorry

end IsConstant

end Constant

section General

variable {D : Type w} [Category.{w'} D]
variable [coefficientMonoidal : MonoidalCategory D]
variable [sliceSheafification : ∀ U : C, HasWeakSheafify (J.over U) D]
variable [ambientMonoidal : MonoidalCategory (Sheaf J D)]
variable [sliceMonoidal : ∀ U : C, MonoidalCategory (Sheaf (J.over U) D)]
variable [restrictionMonoidal : ∀ U : C, Functor.Monoidal (J.overPullback D U)]
variable [constantMonoidal : ∀ U : C, Functor.Monoidal (constantSheaf (J.over U) D)]

/-- The object property of locally constant `D`-valued sheaves. -/
abbrev locallyConstant (J : GrothendieckTopology C) (D : Type w)
    [Category.{w'} D] [∀ U : C, HasWeakSheafify (J.over U) D] :
    ObjectProperty (Sheaf J D) :=
  fun F ↦ IsLocallyConstant F

namespace IsLocallyConstant

/-- Locally constant sheaves valued in a monoidal category are closed under tensor products when
restriction to every slice and the constant-sheaf functors are monoidal. -/
theorem tensor {F G : Sheaf J D} [IsLocallyConstant F] [IsLocallyConstant G] :
    IsLocallyConstant (F ⊗ G) := sorry

end IsLocallyConstant

end General

section Property

variable {D : Type w} [Category.{w'} D]
variable [∀ U : C, HasWeakSheafify (J.over U) D]
variable [MonoidalCategory (Sheaf J D)]

namespace locallyConstant

/-- Tensor product restricts to the object property of locally constant sheaves. -/
instance tensorLE [MonoidalCategory D]
    [∀ U : C, MonoidalCategory (Sheaf (J.over U) D)]
    [∀ U : C, Functor.Monoidal (J.overPullback D U)]
    [∀ U : C, Functor.Monoidal (constantSheaf (J.over U) D)] :
    TensorLE (locallyConstant J D) (locallyConstant J D)
    (locallyConstant J D) := sorry

end locallyConstant

end Property

section Modules

variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]

namespace IsLocallyConstant

/-- Locally constant sheaves of modules over a commutative ring are closed under
the canonical sheaf tensor product. -/
@[stacks 093V]
theorem tensorModule {F G : Sheaf J (ModuleCat.{w} Λ)}
    [IsLocallyConstant F] [IsLocallyConstant G] :
    IsLocallyConstant (F ⊗ G) := sorry

end IsLocallyConstant

end Modules

end CategoryTheory.Sheaf
