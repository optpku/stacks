module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.QuasiIso

/-!
# Derived localization of enriched cochain homotopy categories

This leaf composes the enriched-to-ordinary homotopy comparison with Mathlib's derived
localization.  The quasi-isomorphism system itself is owned by `Homotopy.QuasiIso`.
-/

@[expose] public section

noncomputable section

universe r u v w

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched.Over

variable {R : Type r} [CommRing R]
variable {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
variable [HasDerivedCategory.{w} A]

/-- The canonical functor from the explicit `R`-linear cochain homotopy category to Mathlib's
derived category. -/
@[stacks 09KX "derived localization over a linear base ring"]
abbrev derivedQ :
    DifferentialGradedCategory.K R (CochainComplex A ℤ) ⥤ DerivedCategory.{w} A :=
  toMathlib (R := R) ⋙ DerivedCategory.Qh

/-- The enriched-to-derived localization is `R`-linear over the coefficient ring. -/
@[stacks 09KX "linearity of the enriched derived localization"]
noncomputable instance derivedQ_linear :
    (derivedQ (R := R) (A := A)).Linear R := sorry

/-- The explicit `R`-linear enriched homotopy presentation of a complex has the canonical image
of that complex in the derived category. -/
@[stacks 09KX "enriched localization object comparison over a linear base ring"]
noncomputable def derivedQObjIso (K : CochainComplex A ℤ) :
    (derivedQ (R := R) (A := A)).obj
        (⟨K⟩ : DifferentialGradedCategory.K R (CochainComplex A ℤ)) ≅
      DerivedCategory.Q.obj K :=
  (DerivedCategory.quotientCompQhIso A).app K

/-- The explicit `R`-linear enriched-to-derived functor localizes at enriched cochain
quasi-isomorphisms. -/
@[stacks 09KX "enriched cochain derived localization over a linear base ring"]
instance derivedQIsLocalization :
    (derivedQ (R := R) (A := A)).IsLocalization (quasiIso (R := R) (A := A)) := sorry

end CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{w} A]

/-- Integral specialization of the explicit-base-ring enriched-to-derived functor. -/
@[stacks 09KX "integral enriched derived localization"]
abbrev derivedQ :
    DifferentialGradedCategory.K ℤ (CochainComplex A ℤ) ⥤ DerivedCategory.{w} A :=
  Over.derivedQ (R := ℤ) (A := A)

/-- Integral specialization of the enriched localization object comparison. -/
@[stacks 09KX "integral enriched localization object comparison"]
noncomputable abbrev derivedQObjIso (K : CochainComplex A ℤ) :
    derivedQ.obj (⟨K⟩ : DifferentialGradedCategory.K ℤ (CochainComplex A ℤ)) ≅
      DerivedCategory.Q.obj K :=
  Over.derivedQObjIso (R := ℤ) (A := A) K

/-- Compatibility name for the integral enriched derived localization instance. -/
@[stacks 09KX "integral enriched derived localization instance"]
abbrev derivedQIsLocalization :
    (derivedQ (A := A)).IsLocalization (quasiIso (A := A)) := inferInstance

end CategoryTheory.CochainComplex.Enriched
