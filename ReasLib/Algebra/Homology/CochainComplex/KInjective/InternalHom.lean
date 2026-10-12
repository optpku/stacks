/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-injective canonical internal Homs of cochain complexes

This leaf owns the coefficient-category-generic criterion for the explicit cochain internal-Hom
construction.  The target is `CochainComplex.InternalHom.obj`, rather than an arbitrary
`MonoidalClosed` instance on cochain complexes, so the internal Hom and the tensor used by
K-flatness are the same canonical construction.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory.CochainComplex.InternalHom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
variable [HasZeroObject C] [HasProductsOfShape ℤ C]
variable [∀ X Y : GradedObject ℤ C, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ X Y Z W : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X Y Z W]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]

/-- Lemma 21.34.8 (0A96): a K-flat source and a K-injective target have a K-injective
canonical cochain internal-Hom complex. -/
@[stacks 0A96 "canonical K-injective internal-Hom criterion"]
theorem isKInjective_of_isKFlat
    (L I : CochainComplex C ℤ) (hL : L.IsKFlat) [I.IsKInjective] :
    (obj L I).IsKInjective := sorry

end CategoryTheory.CochainComplex.InternalHom

end
