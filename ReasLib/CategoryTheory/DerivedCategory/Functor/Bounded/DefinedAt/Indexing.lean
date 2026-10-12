/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso.Bounded.Refinement
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Inclusion
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Projection
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded and unbounded derived indexing diagrams

The bounded-below and bounded-above localization-comma diagrams become the corresponding
unbounded diagrams after applying the canonical bounded derived inclusion.  These comparisons
specialize the neutral localizer-morphism projection API and hide all associators and
whiskerings from downstream derived-functor arguments.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace RightDerived.Value

/-- Stacks 05T5: the unbounded right-derived indexing diagram restricted from `K(A)` to
`K⁺(A)` agrees, after inclusion, with the bounded-below indexing diagram. -/
@[stacks 05T5 "bounded-below right-derived indexing comparison"]
noncomputable def boundedBelowDiagramIso (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Plus A) :
    (HomotopyCategory.Plus.Ambient.localizerMorphism A).costructuredArrow K ⋙
        (CostructuredArrow.proj (HomotopyCategory.quasiIso A (up ℤ)).Q
          ((HomotopyCategory.quasiIso A (up ℤ)).Q.obj K.obj) ⋙
            Functor.Homotopy.toDerived F) ≅
      (CostructuredArrow.proj (HomotopyCategory.Plus.quasiIso A).Q
          ((HomotopyCategory.Plus.quasiIso A).Q.obj K) ⋙
            F.toBoundedBelowDerived) ⋙ DerivedCategory.Plus.ι :=
  LocalizerMorphism.costructuredArrow.diagramIsoOfIso
    (HomotopyCategory.Plus.Ambient.localizerMorphism A) K
    (Functor.toBoundedBelowDerived.compInclusionIso F).symm

namespace boundedBelowDiagramIso

/-- Every forward component of the bounded-below indexing comparison is the identity. -/
@[simp]
theorem hom_app (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Plus A)
    (U : CostructuredArrow (HomotopyCategory.Plus.quasiIso A).Q
      ((HomotopyCategory.Plus.quasiIso A).Q.obj K)) :
    (boundedBelowDiagramIso F K).hom.app U = 𝟙 _ := sorry

/-- Every inverse component of the bounded-below indexing comparison is the identity. -/
@[simp]
theorem inv_app (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Plus A)
    (U : CostructuredArrow (HomotopyCategory.Plus.quasiIso A).Q
      ((HomotopyCategory.Plus.quasiIso A).Q.obj K)) :
    (boundedBelowDiagramIso F K).inv.app U = 𝟙 _ := sorry

end boundedBelowDiagramIso

end RightDerived.Value

namespace LeftDerived.Value

/-- Stacks 05T5: the unbounded left-derived indexing diagram restricted from `K(A)` to
`K⁻(A)` agrees, after inclusion, with the bounded-above indexing diagram. -/
@[stacks 05T5 "bounded-above left-derived indexing comparison"]
noncomputable def boundedAboveDiagramIso (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Minus A) :
    (HomotopyCategory.Minus.Ambient.localizerMorphism A).structuredArrow K ⋙
        (StructuredArrow.proj
          ((HomotopyCategory.quasiIso A (up ℤ)).Q.obj K.obj)
            (HomotopyCategory.quasiIso A (up ℤ)).Q ⋙
              Functor.Homotopy.toDerived F) ≅
      (StructuredArrow.proj
          ((HomotopyCategory.Minus.quasiIso A).Q.obj K)
            (HomotopyCategory.Minus.quasiIso A).Q ⋙
              F.toBoundedAboveDerived) ⋙ DerivedCategory.Minus.ι :=
  LocalizerMorphism.structuredArrow.diagramIsoOfIso
    (HomotopyCategory.Minus.Ambient.localizerMorphism A) K
    (Functor.toBoundedAboveDerived.compInclusionIso F).symm

namespace boundedAboveDiagramIso

/-- Every forward component of the bounded-above indexing comparison is the identity. -/
@[simp]
theorem hom_app (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Minus A)
    (U : StructuredArrow ((HomotopyCategory.Minus.quasiIso A).Q.obj K)
      (HomotopyCategory.Minus.quasiIso A).Q) :
    (boundedAboveDiagramIso F K).hom.app U = 𝟙 _ := sorry

/-- Every inverse component of the bounded-above indexing comparison is the identity. -/
@[simp]
theorem inv_app (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Minus A)
    (U : StructuredArrow ((HomotopyCategory.Minus.quasiIso A).Q.obj K)
      (HomotopyCategory.Minus.quasiIso A).Q) :
    (boundedAboveDiagramIso F K).inv.app U = 𝟙 _ := sorry

end boundedAboveDiagramIso

end LeftDerived.Value



end CategoryTheory.Functor
