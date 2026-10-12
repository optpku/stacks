/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tor from derived tensor

The source-facing `Tor` owner is homology of the genuine two-variable derived tensor bifunctor.
The one-sided `Left` and `Right` views remain available under explicit names; keeping the
orientation visible prevents a fixed-factor construction from being mistaken for a symmetric Tor
object.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [hB : Has (C := C)]

include hB

/-- The two-variable Tor functor obtained by applying degree `-p` homology to derived tensor. -/
@[stacks 08BP "two-variable Tor functor"]
noncomputable abbrev torFunctor (p : ℕ) :
    DerivedCategory C × DerivedCategory C ⥤ C :=
  functor (C := C) ⋙ DerivedCategory.homologyFunctor C (-(p : ℤ))

/-- The fixed-right view of the two-variable Tor functor. -/
@[stacks 08BP "two-variable fixed-right Tor functor"]
noncomputable abbrev torRightFunctor (p : ℕ) (L : DerivedCategory C) :
    DerivedCategory C ⥤ C :=
  rightFunctor L ⋙ DerivedCategory.homologyFunctor C (-(p : ℤ))

/-- The fixed-left view of the two-variable Tor functor. -/
@[stacks 08BP "two-variable fixed-left Tor functor"]
noncomputable abbrev torLeftFunctor (p : ℕ) (K : DerivedCategory C) :
    DerivedCategory C ⥤ C :=
  leftFunctor K ⋙ DerivedCategory.homologyFunctor C (-(p : ℤ))

/-- The `p`-th Tor object of arbitrary derived objects, using the two-variable derived tensor. -/
@[stacks 08BP "Tor from the derived tensor bifunctor"]
noncomputable abbrev torObj (p : ℕ) (K L : DerivedCategory C) : C :=
  (torFunctor p).obj (K, L)

/-- The `p`-th Tor object of two ordinary objects, viewed in degree zero. -/
@[stacks 08BP "degree-zero Tor from the derived tensor bifunctor"]
noncomputable abbrev tor (p : ℕ) (F G : C) : C :=
  torObj p ((DerivedCategory.singleFunctor C (0 : ℤ)).obj F)
    ((DerivedCategory.singleFunctor C (0 : ℤ)).obj G)

end CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor

namespace CategoryTheory.DerivedCategory.DerivedTensor

section OneSided

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ (K L : CochainComplex C ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]

/-- The fixed-right Tor functor, deriving the first tensor factor. -/
@[stacks 08BP "fixed-right Tor functor"]
noncomputable abbrev torRightFunctor (p : ℕ) (L : DerivedCategory C)
    [Right.Has (C := C)] : DerivedCategory C ⥤ C :=
  Right.functor L ⋙ DerivedCategory.homologyFunctor C (-(p : ℤ))

/-- Tor computed with the first variable derived and the second variable fixed. -/
@[stacks 08BP "fixed-right Tor presentation"]
noncomputable abbrev torRightObj (p : ℕ) (K L : DerivedCategory C)
    [Right.Has (C := C)] : C :=
  (torRightFunctor p L).obj K

/-- Degree-zero Tor in the fixed-right presentation. -/
@[stacks 08BP "degree-zero fixed-right Tor presentation"]
noncomputable abbrev torRight (p : ℕ) (F G : C) [Right.Has (C := C)] : C :=
  torRightObj p ((DerivedCategory.singleFunctor C (0 : ℤ)).obj F)
    ((DerivedCategory.singleFunctor C (0 : ℤ)).obj G)

/-- The fixed-left Tor functor, deriving the second tensor factor. -/
@[stacks 08BP "fixed-left Tor functor"]
noncomputable abbrev torLeftFunctor (p : ℕ) (K : DerivedCategory C)
    [Left.Has (C := C)] : DerivedCategory C ⥤ C :=
  Left.functor K ⋙ DerivedCategory.homologyFunctor C (-(p : ℤ))

/-- Tor computed with the second variable derived and the first variable fixed. -/
@[stacks 08BP "fixed-left Tor presentation"]
noncomputable abbrev torLeftObj (p : ℕ) (K L : DerivedCategory C)
    [Left.Has (C := C)] : C :=
  (torLeftFunctor p K).obj L

/-- Degree-zero Tor in the fixed-left presentation. -/
@[stacks 08BP "degree-zero fixed-left Tor presentation"]
noncomputable abbrev torLeft (p : ℕ) (F G : C) [Left.Has (C := C)] : C :=
  torLeftObj p ((DerivedCategory.singleFunctor C (0 : ℤ)).obj F)
    ((DerivedCategory.singleFunctor C (0 : ℤ)).obj G)

end OneSided

end CategoryTheory.DerivedCategory.DerivedTensor

namespace DerivedTor

/-- Scoped notation for the source-facing two-variable Tor object. -/
scoped notation:max "Tor[" p "](" F ", " G ")" =>
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.tor p F G

end DerivedTor

end
