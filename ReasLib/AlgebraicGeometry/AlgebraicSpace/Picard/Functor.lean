/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Stack
public import ReasLib.CategoryTheory.CategoryOfElements.Section
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.CategoryOfElements.Forward
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The classifying morphism to the relative Picard sheaf

The classifying morphism sends a Picard object to its fibrewise isomorphism
class, then to its Picard class and its image in the relative fppf sheafification.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The fppf sheaf on schemes over `S` obtained by sheafifying fibrewise
isomorphism classes of the Picard projection. -/
def functorOver (f : X ⟶ B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (Functor.fiberIsoClassPresheaf (Picard.p f))

end AlgebraicGeometry.AlgebraicSpace.RelativePicard

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The classifying functor sends an invertible module on a fibre to its
section of the relative Picard sheaf. -/
def classifyingFunctor (f : X ⟶ B) : Obj f ⥤ (picardFunctor f).obj.Elementsᵒᵖ :=
  CategoryOfElements.Section.functor (toSchemesOver f)
      (Functor.fiberIsoClassPresheaf (toSchemesOver f))
      (Functor.fiberIsoClassPresheaf.tautologicalSection (toSchemesOver f)) ⋙
    (CategoryOfElements.map
      (fiberIsoClassToPresheaf f ≫
        (sheafificationAdjunction (SchemesOver.fppfTopology B) (Type (u + 1))).unit.app
          (RelativePicard.presheaf f))).op

/-- The classifying functor commutes strictly with the projection to schemes
over the target. -/
theorem classifyingFunctor_comp_projection (f : X ⟶ B) :
    classifyingFunctor f ⋙ (CategoryOfElements.π (picardFunctor f).obj).leftOp =
      toSchemesOver f := sorry

/-- The canonical cartesian morphism from the Picard category to the category
of elements of the relative Picard sheaf. -/
def toFunctor (f : X ⟶ B) :
    CartesianBasedFunctor (toSchemesOver f)
      ((CategoryOfElements.π (picardFunctor f).obj).leftOp) :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (classifyingFunctor f) (classifyingFunctor_comp_projection f))

/-- The image of a Picard object is its Picard class followed by the canonical
unit of fppf sheafification. -/
theorem toFunctor_obj (f : X ⟶ B) (x : Obj f) :
    (toFunctor f).toBasedFunctor.toFunctor.obj x =
      op ((picardFunctor f).obj.elementsMk (op x.σ)
        (((sheafificationAdjunction (SchemesOver.fppfTopology B) (Type (u + 1))).unit.app
            (RelativePicard.presheaf f)).app (op x.σ)
          ((fiberIsoClassToPresheaf f).app (op x.σ) (Quotient.mk'' ⟨x, rfl⟩)))) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
