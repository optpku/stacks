module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import ReasLib.CategoryTheory.Sites.Cech.Additive
public import ReasLib.CategoryTheory.Sites.Cech.FreeAbelian
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Presheaf.Cech.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of Cech complexes

Restriction to a slice is exact without additive hypotheses.  For an Abelian
coefficient category, the Cech-complex functor is left exact as soon as the
required products exist; exactness of those products is needed only for the
right exact and exact declarations.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe w vA uA v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Restriction of presheaves to a slice is exact because it is precomposition with the slice
forgetful functor. -/
@[stacks 03AP "exact restriction of presheaves to a slice"]
theorem restrictPresheafToOver_exact
    {A : Type uA} [Category.{vA} A] (U : C) :
    exactFunctor (Cᵒᵖ ⥤ A) ((Over U)ᵒᵖ ⥤ A) (restrictPresheafToOver U) := sorry

namespace Cech

variable {A : Type uA} [Category.{vA} A]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)
variable [HasProducts.{w} A]

section LeftExact

variable [Preadditive A] [HasFiniteLimits A]

/-- The Cech-complex functor is left exact whenever its required products exist. -/
@[stacks 03AQ "left exactness of the Cech-complex functor"]
theorem complexFunctor_leftExact :
    leftExactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ)
      (cechComplexOnPresheaves U family) := sorry

/-- The Cech-complex functor bundled with its left exactness property. -/
@[stacks 03AQ "bundled left exact Cech-complex functor"]
noncomputable def complexLeftExactFunctor :
    LeftExactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ) :=
  ⟨cechComplexOnPresheaves U family, complexFunctor_leftExact U family⟩

end LeftExact

section Exact

variable [Abelian A] [AB4StarOfSize.{w} A]

/-- The Cech-complex functor is right exact when its required products are exact. -/
@[stacks 03AQ "right exactness of the Cech-complex functor"]
theorem complexFunctor_rightExact :
    rightExactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ)
      (cechComplexOnPresheaves U family) := sorry

/-- The Cech-complex functor bundled with its right exactness property. -/
@[stacks 03AQ "bundled right exact Cech-complex functor"]
noncomputable def complexRightExactFunctor :
    RightExactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ) :=
  ⟨cechComplexOnPresheaves U family, complexFunctor_rightExact U family⟩

/-- The Cech-complex functor associated to a family in `Over U` is exact for presheaves valued in
`A` when its required products are exact. -/
@[stacks 03AQ]
theorem complexFunctor_exact :
    exactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ)
      (cechComplexOnPresheaves U family) := sorry

/-- The Cech-complex functor bundled with its exactness property. -/
@[stacks 03AQ "bundled exact Cech-complex functor"]
noncomputable def complexExactFunctor :
    ExactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ) :=
  ⟨cechComplexOnPresheaves U family, complexFunctor_exact U family⟩

/-- A short exact sequence of presheaves induces a short exact sequence of Cech complexes. -/
@[stacks 03AQ "short exact sequences of Cech complexes"]
theorem map_shortExact {S : ShortComplex (Cᵒᵖ ⥤ A)}
    (hS : S.ShortExact) :
    (S.map (cechComplexOnPresheaves U family)).ShortExact := sorry

end Exact

end Cech

namespace Cech.FixedTarget

open CategoryTheory.Limits

variable {U : C} {ι : Type w}
variable (family : ι → Over U)
variable [HasIteratedFiberProducts family]
variable [HasProducts.{w} AddCommGrpCat.{max u v}]

/-- The fixed-target Cech cochain functor on additive presheaves, with no global finite-product
assumption on `Over U`. -/
abbrev cochainFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ :=
  restrictPresheafToOver U ⋙
    FormalCoproduct.cochainComplexFunctor (A := AddCommGrpCat.{max u v}) (familyCech family)

/-- The fixed-target Cech cochain functor is exact in its additive presheaf coefficient. -/
@[stacks 03AQ "exact fixed-target Cech cochain functor"]
theorem cochainFunctor_exact :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
      (CochainComplex AddCommGrpCat.{max u v} ℕ) (cochainFunctor family) := sorry

end Cech.FixedTarget

end CategoryTheory
