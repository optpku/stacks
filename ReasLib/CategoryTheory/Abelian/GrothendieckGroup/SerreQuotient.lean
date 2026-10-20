module

public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Functor
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.TwoPeriodic
public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import Mathlib.Algebra.Exact.Basic

/-!
# Grothendieck Groups of Serre Quotients

The Grothendieck groups of a Serre subcategory, its ambient abelian category, and the canonical
Serre quotient form the expected localization sequence.  The kernel of the first map also admits
the classical two-periodic homology description.
-/

@[expose] public section

open CategoryTheory Limits
open ComplexShape

noncomputable section

universe u v

namespace CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

/-- The Grothendieck-group homomorphism induced by inclusion of the Serre subcategory. -/
@[stacks 02MX]
abbrev inclusionK0 :
    AbelianK0 P.FullSubcategory →+ AbelianK0 A :=
  AbelianK0.map (inclusionExactFunctor P)

/-- The Grothendieck-group homomorphism induced by the canonical Serre quotient. -/
@[stacks 02MX]
abbrev quotientK0 :
    AbelianK0 A →+ AbelianK0 P.isoModSerre.Localization :=
  AbelianK0.map (quotientExactFunctor P)

/-- The inclusion map on Grothendieck groups sends a subcategory object to its ambient class. -/
@[simp]
theorem inclusionK0_of (X : P.FullSubcategory) :
    inclusionK0 P K₀[X] = K₀[X.1] := sorry

/-- The quotient map on Grothendieck groups sends an object class to its localized class. -/
@[simp]
theorem quotientK0_of (X : A) :
    quotientK0 P K₀[X] = K₀[P.isoModSerre.Q.obj X] := sorry

/-- The quotient map vanishes after the Grothendieck-group map induced by inclusion. -/
@[simp]
theorem quotientK0_comp_inclusionK0 :
    AddMonoidHom.comp (quotientK0 P) (inclusionK0 P) = 0 := sorry

/-- The image of the Serre-subcategory Grothendieck group is the kernel of the quotient map. -/
@[stacks 02MX]
theorem k0_exact : Function.Exact (inclusionK0 P) (quotientK0 P) := sorry

/-- The Grothendieck-group homomorphism induced by the Serre quotient is surjective. -/
@[stacks 02MX]
theorem quotientK0_surjective : Function.Surjective (quotientK0 P) := sorry

/-- A class lies in the kernel of the Serre-subcategory inclusion exactly when it is the
difference of the two homology classes of a two-periodic endomorphism that becomes acyclic in the
Serre quotient. -/
@[stacks 02MX]
theorem mem_ker_inclusionK0_iff (x : AbelianK0 P.FullSubcategory) :
    x ∈ (inclusionK0 P).ker ↔
      ∃ K : TwoPeriodicEndomorphism A,
        ∃ hQ : ((P.isoModSerre.Q.mapHomologicalComplex (up (ZMod 2))).obj
          K.toCochainComplex).Acyclic,
          x = K₀[acyclicHomology P hQ 0] - K₀[acyclicHomology P hQ 1] := sorry

end CategoryTheory.ObjectProperty.SerreClassLocalization
