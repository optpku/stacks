module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Regular
public import ReasLib.Algebra.Homology.CochainDGAlgebra.HomologyZero
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The ordinary endomorphism algebra of the regular derived object

The graded self-extension comparison is most useful downstream after its degree-zero part has
been exposed as an ordinary algebra map.  This leaf owns that transport and keeps the chosen
zero-shift comparison out of Morita statements.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe u v

namespace DifferentialGradedModule.Derived

variable {R : Type u} [CommRing R]

/-- The degree-zero regular self-extension map, viewed as an ordinary endomorphism. -/
@[stacks 09S8 "degree-zero regular self-extension map"]
noncomputable def regularSelfExtZeroMap (A : CochainDGAlgebra.{u, v} R) :
    A.homologyZero →ₗ[R] End (regularObject A) where
  toFun x :=
    (shiftFunctorZero (Category.{u, v} A) ℤ).inv.app (regularObject A) ≫
      (ShiftedHom.sourceShiftEquiv (regularObject A) (regularObject A) 0)
        (regularSelfExtLinearMap A 0 x)
  map_add' := sorry
  map_smul' := sorry

/-- The degree-zero regular self-extension map evaluates by the canonical zero-shift transport. -/
@[simp]
theorem regularSelfExtZeroMap_apply (A : CochainDGAlgebra.{u, v} R)
    (x : A.homologyZero) :
    regularSelfExtZeroMap A x =
      (shiftFunctorZero (Category.{u, v} A) ℤ).inv.app (regularObject A) ≫
        (ShiftedHom.sourceShiftEquiv (regularObject A) (regularObject A) 0)
          (regularSelfExtLinearMap A 0 x) := rfl

/-- The ordinary algebra map from zeroth cohomology to endomorphisms of the regular object. -/
@[stacks 09S8 "zeroth cohomology algebra map to regular endomorphisms"]
noncomputable def regularEndAlgHom (A : CochainDGAlgebra.{u, v} R) :
    A.homologyZero →ₐ[R] End (regularObject A) where
  toFun := regularSelfExtZeroMap A
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry
  commutes' := sorry

/-- The regular endomorphism algebra map is the degree-zero part of the regular self-Ext map. -/
@[simp]
theorem regularEndAlgHom_apply (A : CochainDGAlgebra.{u, v} R)
    (x : A.homologyZero) :
    regularEndAlgHom A x = regularSelfExtZeroMap A x := rfl

/-- The regular endomorphism algebra map is bijective. -/
@[stacks 09S8 "regular endomorphism algebra comparison is bijective"]
theorem regularEndAlgHom_bijective (A : CochainDGAlgebra.{u, v} R) :
    Function.Bijective (regularEndAlgHom A) := sorry

/-- The canonical algebra equivalence from zeroth cohomology to regular derived endomorphisms. -/
@[stacks 09S8 "regular endomorphism algebra equivalence"]
noncomputable def regularEndAlgEquiv (A : CochainDGAlgebra.{u, v} R)
    : A.homologyZero ≃ₐ[R] End (regularObject A) :=
  AlgEquiv.ofBijective (regularEndAlgHom A) (regularEndAlgHom_bijective A)

/-- A regular endomorphism algebra equivalence built from an explicit bijectivity certificate. -/
@[stacks 09S8 "regular endomorphism algebra equivalence from a bijectivity certificate"]
noncomputable def regularEndAlgEquivOfBijective (A : CochainDGAlgebra.{u, v} R)
    (h : Function.Bijective (regularEndAlgHom A)) :
    A.homologyZero ≃ₐ[R] End (regularObject A) :=
  AlgEquiv.ofBijective (regularEndAlgHom A) h

end DifferentialGradedModule.Derived
