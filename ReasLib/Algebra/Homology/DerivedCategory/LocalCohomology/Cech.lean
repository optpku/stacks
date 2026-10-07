module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Cech
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.RingTheory.Ideal.FiniteGeneration.Family

/-!
# Local cohomology from an extended alternating Cech complex

For a finite family generating an ideal `I`, derived tensor with its extended alternating Cech
complex lands in the full subcategory of derived modules with `I`-power-torsion cohomology. This
file records the lifted functor, its comparison with derived tensor, and its adjunction with the
subcategory inclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open DerivedCategory.CechCompletion

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Derived tensor with the extended alternating Cech complex of a generating family has
ideal-power-torsion cohomology. -/
theorem cechTensor_mem {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I)
    (K : DerivedCategory (ModuleCat A)) :
    cohomologyIn (ModuleCat.isIdealPowerTorsion I)
      ((DerivedTensor.Left.functor (source f)).obj K) := sorry

/-- The functor obtained by lifting derived tensor with an extended alternating Cech complex to
the full subcategory of derived modules with ideal-power-torsion cohomology. -/
noncomputable def cechFunctor {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I) :
    DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I :=
  (cohomologyIn (ModuleCat.isIdealPowerTorsion I)).lift
    (DerivedTensor.Left.functor (source f)) (cechTensor_mem I f hgen)

/-- After inclusion into the ambient derived category, the lifted Cech functor is canonically
isomorphic to derived tensor with the extended alternating Cech complex. -/
noncomputable def cechFunctorCompιIso {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I) :
    cechFunctor I f hgen ⋙ IdealPowerTorsion.inclusion I ≅
      DerivedTensor.Left.functor (source f) :=
  (cohomologyIn (ModuleCat.isIdealPowerTorsion I)).liftCompιIso
    (DerivedTensor.Left.functor (source f)) (cechTensor_mem I f hgen)

/-- Forgetting the ideal-power-torsion condition identifies the value of the lifted Cech functor
with derived tensor by the extended alternating Cech complex. -/
theorem cechFunctor_obj {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I)
    (K : DerivedCategory (ModuleCat A)) :
    ((cechFunctor I f hgen).obj K).obj =
      (DerivedTensor.Left.functor (source f)).obj K := sorry

/-- The lifted Cech functor of a finite generating family is right adjoint to the inclusion of
derived modules with ideal-power-torsion cohomology. -/
theorem cechAdjunction {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I) :
    Nonempty (IdealPowerTorsion.inclusion I ⊣ cechFunctor I f hgen) := sorry

/-- The inclusion of derived modules with ideal-power-torsion cohomology for a finitely generated
ideal admits a right adjoint. -/
theorem existsRightAdjoint (I : Ideal A) (hI : I.FG) :
    ∃ RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I,
      Nonempty (IdealPowerTorsion.inclusion I ⊣ RΓ) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
