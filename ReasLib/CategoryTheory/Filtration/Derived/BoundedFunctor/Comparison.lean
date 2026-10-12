/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.AssociatedGraded
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Minus
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Inclusion
public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
public import ReasLib.CategoryTheory.Filtration.Derived.Forget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-to-unbounded comparisons for finite filtered functors

The bounded filtered functors are defined on full subcategories of the ordinary finite filtered
derived category.  This leaf records the canonical comparisons after forgetting boundedness.  The
source category is only preadditive; in particular, no abelian structure is imposed on finite
filtered objects merely to obtain these comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

section Finite

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]

namespace Plus.AssociatedGraded

/-- The bounded-below associated-graded homotopy functor agrees with the ambient one after
including `D⁺(Gr(C))` into `D(Gr(C))`. -/
@[stacks 05S6 "bounded finite filtered associated-graded comparison"]
noncomputable def compInclusionIso :
    homotopy C ⋙
        (DerivedCategory.Plus.ι :
          DerivedCategory.Plus (GradedObject ℤ C) ⥤ DerivedCategory (GradedObject ℤ C)) ≅
      (HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)) ⋙
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy C) :=
  Functor.toBoundedBelowDerived.compInclusionIso
    (FilteredObject.Finite.AssociatedGraded.functor C)

end Plus.AssociatedGraded

namespace Minus.AssociatedGraded

/-- The bounded-above associated-graded homotopy functor agrees with the ambient one after
including `D⁻(Gr(C))` into `D(Gr(C))`. -/
@[stacks 05S6 "bounded finite filtered associated-graded comparison"]
noncomputable def compInclusionIso :
    homotopy C ⋙
        (DerivedCategory.Minus.ι :
          DerivedCategory.Minus (GradedObject ℤ C) ⥤ DerivedCategory (GradedObject ℤ C)) ≅
      (HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)) ⋙
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy C) :=
  Functor.toBoundedAboveDerived.compInclusionIso
    (FilteredObject.Finite.AssociatedGraded.functor C)

end Minus.AssociatedGraded

namespace Bounded.AssociatedGraded

/-- The bounded associated-graded homotopy functor agrees with the ambient one after including
`Dᵇ(Gr(C))` into `D(Gr(C))`. -/
@[stacks 05S6 "bounded finite filtered associated-graded comparison"]
noncomputable def compInclusionIso :
    homotopy C ⋙
        (DerivedCategory.Bounded.ι :
          DerivedCategory.Bounded (GradedObject ℤ C) ⥤ DerivedCategory (GradedObject ℤ C)) ≅
      (HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)) ⋙
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy C) :=
  Functor.toBoundedDerived.compInclusionIso
    (FilteredObject.Finite.AssociatedGraded.functor C)

end Bounded.AssociatedGraded

namespace Plus.GradedPiece

/-- The bounded-below finite filtered graded-piece homotopy functor agrees with the ambient
graded-piece homotopy functor after including `D⁺(C)` into `D(C)`. -/
@[stacks 05S6 "bounded finite filtered graded-piece comparison"]
noncomputable def compInclusionIso (p : ℤ) :
    homotopy C p ⋙ (DerivedCategory.Plus.ι : DerivedCategory.Plus C ⥤ DerivedCategory C) ≅
      (HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)) ⋙
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy C p) :=
  Functor.toBoundedBelowDerived.compInclusionIso
      (FilteredObject.Finite.AssociatedGraded.functor C ⋙ GradedObject.eval p) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.Homotopy.Comp.iso
        (FilteredObject.Finite.AssociatedGraded.functor C) (GradedObject.eval p))

end Plus.GradedPiece

namespace Plus.Forget

/-- The bounded-below finite filtered forgetful homotopy functor agrees with the ambient
forgetful homotopy functor after including `D⁺(C)` into `D(C)`. -/
@[stacks 05S6 "bounded finite filtered forgetful comparison"]
noncomputable def compInclusionIso :
    homotopy C ⋙ (DerivedCategory.Plus.ι : DerivedCategory.Plus C ⥤ DerivedCategory C) ≅
      (HomotopyCategory.Plus.ι (FilteredObject.Finite.category C)) ⋙
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy C) :=
  Functor.toBoundedBelowDerived.compInclusionIso (FilteredObject.Finite.Forget.functor C)

end Plus.Forget

namespace Minus.GradedPiece

/-- The bounded-above finite filtered graded-piece homotopy functor agrees with the ambient
graded-piece homotopy functor after including `D⁻(C)` into `D(C)`. -/
@[stacks 05S6 "bounded finite filtered graded-piece comparison"]
noncomputable def compInclusionIso (p : ℤ) :
    homotopy C p ⋙ (DerivedCategory.Minus.ι : DerivedCategory.Minus C ⥤ DerivedCategory C) ≅
      (HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)) ⋙
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy C p) :=
  Functor.toBoundedAboveDerived.compInclusionIso
      (FilteredObject.Finite.AssociatedGraded.functor C ⋙ GradedObject.eval p) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.Homotopy.Comp.iso
        (FilteredObject.Finite.AssociatedGraded.functor C) (GradedObject.eval p))

end Minus.GradedPiece

namespace Minus.Forget

/-- The bounded-above finite filtered forgetful homotopy functor agrees with the ambient
forgetful homotopy functor after including `D⁻(C)` into `D(C)`. -/
@[stacks 05S6 "bounded finite filtered forgetful comparison"]
noncomputable def compInclusionIso :
    homotopy C ⋙ (DerivedCategory.Minus.ι : DerivedCategory.Minus C ⥤ DerivedCategory C) ≅
      (HomotopyCategory.Minus.ι (FilteredObject.Finite.category C)) ⋙
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy C) :=
  Functor.toBoundedAboveDerived.compInclusionIso (FilteredObject.Finite.Forget.functor C)

end Minus.Forget

namespace Bounded.GradedPiece

/-- The bounded finite filtered graded-piece homotopy functor agrees with the ambient graded-piece
homotopy functor after including `Dᵇ(C)` into `D(C)`. -/
@[stacks 05S6 "bounded finite filtered graded-piece comparison"]
noncomputable def compInclusionIso (p : ℤ) :
    homotopy C p ⋙ (DerivedCategory.Bounded.ι : DerivedCategory.Bounded C ⥤ DerivedCategory C) ≅
      (HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)) ⋙
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy C p) :=
  Functor.toBoundedDerived.compInclusionIso
      (FilteredObject.Finite.AssociatedGraded.functor C ⋙ GradedObject.eval p) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.Homotopy.Comp.iso
        (FilteredObject.Finite.AssociatedGraded.functor C) (GradedObject.eval p))

end Bounded.GradedPiece

namespace Bounded.Forget

/-- The bounded finite filtered forgetful homotopy functor agrees with the ambient forgetful
homotopy functor after including `Dᵇ(C)` into `D(C)`. -/
@[stacks 05S6 "bounded finite filtered forgetful comparison"]
noncomputable def compInclusionIso :
    homotopy C ⋙ (DerivedCategory.Bounded.ι : DerivedCategory.Bounded C ⥤ DerivedCategory C) ≅
      (HomotopyCategory.Bounded.ι (FilteredObject.Finite.category C)) ⋙
        (_root_.CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy C) :=
  Functor.toBoundedDerived.compInclusionIso (FilteredObject.Finite.Forget.functor C)

end Bounded.Forget

end Finite

end CategoryTheory.FilteredObject.FiniteDerived
