module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.CategoryTheory.Abelian.GrothendieckCategory.FunctorCategory
public import ReasLib.CategoryTheory.Sites.Cech.DeltaFunctor
public import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived-functor comparisons for Cech cohomology

This leaf owns the source-specific comparison between Cech cohomology and the ordinary right
derived functors of its degree-zero branch. The generic injective-resolution computation remains
owned by `InjectiveResolution.isoRightDerivedObj`; universality criteria live in the independent
`Cech.Universal` leaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w vA uA v u

namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)
variable [HasProducts.{w} A] [AB4StarOfSize.{w} A]
variable [HasInjectiveResolutions (Cᵒᵖ ⥤ A)]

/-- Positive Čech cohomology is naturally isomorphic to the corresponding ordinary right
derived functor of degree-zero Čech cohomology. -/
@[stacks 03AU "Cech cohomology as a right derived functor"]
theorem cohomologyFunctor_isIsomorphic_rightDerived (p : ℕ) :
    IsIsomorphic ((cohomologyFunctor (A := A) U family (p + 1)).obj)
      (((cohomologyFunctor (A := A) U family 0).obj).rightDerived (p + 1)) := sorry

/-- The Čech complex of a presheaf admits a quasi-isomorphism to the complex obtained by
applying degree-zero Čech cohomology to an injective resolution. -/
@[stacks 03AU "Cech complex comparison with an injective resolution"]
theorem complex_quasiIso_to_cohomologyZero
    (F : Cᵒᵖ ⥤ A) (I : InjectiveResolution F) :
    ∃ φ : (cechComplexOnPresheaves U family).obj F ⟶
        (((cohomologyFunctor (A := A) U family 0).obj.mapHomologicalComplex (up ℕ)).obj
          I.cocomplex),
      QuasiIso φ := sorry

end CategoryTheory.Cech

namespace CategoryTheory.Cech.FixedTarget

open CategoryTheory CategoryTheory.Limits
open ComplexShape

variable {C : Type u} [Category.{v} C] {U : C} {ι : Type w}
variable (family : ι → Over U) [HasIteratedFiberProducts family]
variable [HasProducts.{w} AddCommGrpCat.{max u v}]

/-- Fixed-target Čech cohomology is naturally isomorphic in every nonnegative degree to the
right derived functor of its degree-zero branch. -/
@[stacks 03AU "fixed-target Cech cohomology as a right derived functor"]
theorem cohomologyFunctor_isIsomorphic_rightDerived (p : ℕ) :
    IsIsomorphic ((cohomologyFunctor family p).obj)
      (((cohomologyFunctor family 0).obj).rightDerived p) := sorry

/-- The fixed-target Čech complex compares to degree-zero Čech cohomology applied to an
injective resolution. -/
@[stacks 03AU "fixed-target Cech complex comparison with an injective resolution"]
theorem complex_quasiIso_to_cohomologyZero
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (I : InjectiveResolution F) :
    ∃ φ : (cochainFunctor family).obj F ⟶
        (((cohomologyFunctor family 0).obj.mapHomologicalComplex (up ℕ)).obj
          I.cocomplex),
      QuasiIso φ := sorry

end CategoryTheory.Cech.FixedTarget
