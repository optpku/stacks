module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.Homology
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Above Left-Derived Comparisons

This leaf defines the integer cohomology and natural-number homological
degrees of a bounded-above left-derived model.  It also constructs the
degree-zero comparison to the underived functor from a localization counit.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- The cohomology in integer degree `i` of a bounded-above left-derived
model. -/
@[stacks 015A]
abbrev degree (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B)
    (i : ℤ) : A ⥤ B :=
  DerivedCategory.Minus.singleFunctor A 0 ⋙ LF ⋙
    DerivedCategory.Minus.homologyFunctor B i

/-- The homological degree `n` of a bounded-above left-derived model,
defined as its cohomology in degree `-n`. -/
@[stacks 015A]
abbrev homologicalDegree
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B)
    (n : ℕ) : A ⥤ B :=
  degree LF (-(n : ℤ))

namespace degree

/-- Computing a left-derived degree with the localization-model single object
agrees with the canonical degree functor. -/
@[stacks 015A]
noncomputable def fromHomotopyIso
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) (i : ℤ) :
    DerivedCategory.Minus.singleFunctor.fromHomotopy A 0 ⋙ LF ⋙
        DerivedCategory.Minus.homologyFunctor B i ≅
      degree LF i :=
  Functor.isoWhiskerRight
    (DerivedCategory.Minus.singleFunctor.fromHomotopy.iso A 0)
    (LF ⋙ DerivedCategory.Minus.homologyFunctor B i)

end degree

variable (F : A ⥤ B) [F.Additive]
  (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B)
  (ε : DerivedCategory.Minus.Qh A ⋙ LF ⟶ F.toBoundedAboveDerived)

/-- The degree-zero comparison from a bounded-above left-derived model to the
underived functor, constructed from its localization counit. -/
@[stacks 015A]
noncomputable def zero : degree LF 0 ⟶ F :=
  (degree.fromHomotopyIso LF 0).inv ≫
    Functor.whiskerRight
      (Functor.whiskerRight
        (Functor.whiskerLeft (HomotopyCategory.Minus.singleFunctor A 0) ε)
        DerivedCategory.Minus.ι)
      (DerivedCategory.homologyFunctor B 0) ≫
    Functor.whiskerRight
      (Functor.toBoundedAboveDerived.singleIso F 0).hom
      (DerivedCategory.homologyFunctor B 0) ≫
    (Functor.isoWhiskerLeft F
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0)).hom

namespace zero

/-- Naturality of the degree-zero left-derived comparison. -/
@[reassoc (attr := simp), stacks 015A "bounded-above left-derived comparison naturality"]
theorem naturality {X Y : A} (f : X ⟶ Y) :
    (degree LF 0).map f ≫ (zero F LF ε).app Y =
      (zero F LF ε).app X ≫ F.map f := sorry

end zero

end CategoryTheory.Functor.LeftDerived
