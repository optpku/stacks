/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient

/-!
# Conormal objects of invertible quotients

This leaf owns the category-independent kernel-tensor-inverse object attached
to an epimorphism onto an invertible object of a monoidal category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CategoryTheory.InvertibleQuotient

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasZeroMorphisms C] [HasKernels C]

/-- The kernel of an invertible quotient tensored with the chosen tensor inverse of its target. -/
noncomputable def conormalObject {E : C} (q : InvertibleQuotient E) : C :=
  tensorObj (kernel q.hom)
    (@isInvertibleObject.inverse C _ _ q.object q.isInvertible)

/-- Compatible isomorphisms of the sources and targets of two invertible quotients induce an
isomorphism of their kernel-tensor-inverse conormal objects. -/
noncomputable def conormalObjectIso {E E' : C}
    (q : InvertibleQuotient E) (q' : InvertibleQuotient E')
    (sourceIso : E ≅ E') (targetIso : q.object ≅ q'.object)
    (comm : q.hom ≫ targetIso.hom = sourceIso.hom ≫ q'.hom) :
    conormalObject q ≅ conormalObject q' :=
  (kernel.mapIso (f := q.hom) q'.hom sourceIso targetIso comm) ⊗ᵢ
    (@isInvertibleObject.inverseIso C _ _ q.object q.isInvertible
      (@isInvertibleObject.inverse C _ _ q'.object q'.isInvertible)
      (ExactPairing.ofTensorInverse
        ((targetIso ⊗ᵢ Iso.refl _) ≪≫
          @isInvertibleObject.tensorInverseIso C _ _ q'.object q'.isInvertible)
        ((Iso.refl _ ⊗ᵢ targetIso) ≪≫
          @isInvertibleObject.inverseTensorIso C _ _ q'.object q'.isInvertible))).symm

end CategoryTheory.InvertibleQuotient
