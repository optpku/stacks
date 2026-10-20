/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Shift.Linear
public import ReasLib.Algebra.Homology.DifferentialGradedModule.QuasiIso
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient

/-!
# The Derived Category of a Differential Graded Algebra

For a cochain differential graded algebra `A`, this leaf owns the acyclic objects in the
homotopy category, their Verdier quotient, the localization functor, and the homology functors
descended through that localization.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

namespace Homotopy

/-- A differential graded module in the homotopy category is acyclic when its underlying
cochain complex has zero homology in every degree. -/
@[stacks 09KW "acyclic objects in the DG homotopy category"]
def acyclic (A : CochainDGAlgebra R) :
    ObjectProperty (K R (DifferentialGradedModule.{u, v} A)) :=
  fun X ↦ ∀ n : ℤ, IsZero (X.obj.homology n)

namespace Acyclic

/-- A homotopy object is acyclic exactly when all its homology objects vanish. -/
theorem iff (A : CochainDGAlgebra R)
    (X : K R (DifferentialGradedModule.{u, v} A)) :
    acyclic A X ↔ ∀ n : ℤ, IsZero (X.obj.homology n) := sorry

/-- Acyclic differential graded modules form a triangulated object property. -/
instance isTriangulated (A : CochainDGAlgebra R) :
    (acyclic.{u, v} A).IsTriangulated := sorry

/-- Acyclicity is invariant under isomorphism in the homotopy category. -/
instance isClosedUnderIsomorphisms (A : CochainDGAlgebra R) :
    (acyclic.{u, v} A).IsClosedUnderIsomorphisms := sorry

/-- Acyclicity is stable under retracts in the homotopy category. -/
instance isStableUnderRetracts (A : CochainDGAlgebra R) :
    (acyclic.{u, v} A).IsStableUnderRetracts := sorry

/-- Every homology functor inverts the cone-defined morphism system of acyclic objects. -/
theorem trW_isInvertedBy_homologyFunctor (A : CochainDGAlgebra R) (n : ℤ) :
    (acyclic.{u, v} A).trW.IsInvertedBy (homologyFunctor A n) := sorry

end Acyclic

end Homotopy

namespace QuasiIso

/-- Lemma 22.22.1 (09KW): quasi-isomorphisms are exactly the morphisms whose triangulated cone
is acyclic. -/
@[stacks 09KW]
theorem eq_trW (A : CochainDGAlgebra R) :
    quasiIso.{u, v} A = (Homotopy.acyclic A).trW := sorry

/-- Quasi-isomorphisms are compatible with every integer shift. -/
@[stacks 09KW "shift compatibility of DG quasi-isomorphisms"]
instance isCompatibleWithShift (A : CochainDGAlgebra R) :
    (quasiIso.{u, v} A).IsCompatibleWithShift ℤ := sorry

/-- Quasi-isomorphisms in the DG homotopy category form a saturated multiplicative system. -/
@[stacks 09KW "DG quasi-isomorphisms form a saturated multiplicative system"]
instance isSaturatedMultiplicativeSystem (A : CochainDGAlgebra R) :
    MorphismProperty.IsSaturatedMultiplicativeSystem (quasiIso.{u, v} A) := sorry

/-- Quasi-isomorphisms in the DG homotopy category are compatible with the triangulation. -/
@[stacks 09KW "DG quasi-isomorphisms are compatible with triangulation"]
instance isCompatibleWithTriangulation (A : CochainDGAlgebra R) :
    (quasiIso.{u, v} A).IsCompatibleWithTriangulation := sorry

end QuasiIso

namespace Derived

/-- Definition 22.22.2 (09KX): the derived category of `A` is the Verdier quotient of its
differential graded homotopy category by the acyclic objects. -/
@[stacks 09KX]
abbrev Category (A : CochainDGAlgebra R) :=
  CategoryTheory.ObjectProperty.verdierQuotient (Homotopy.acyclic.{u, v} A)

/-- Definition 22.22.2 (09KX): the canonical functor from the differential graded homotopy
category to the derived category. -/
@[stacks 09KX]
abbrev Q (A : CochainDGAlgebra R) :
    K R (DifferentialGradedModule.{u, v} A) ⥤ Category A :=
  CategoryTheory.ObjectProperty.verdierQuotientFunctor (Homotopy.acyclic A)

/-- The canonical localization from the DG homotopy category is additive.  Naming this
specialization keeps composite functors such as `Derived.fromModules A` inferable without local
instance pins. -/
@[stacks 09KX "additivity of the DG derived localization"]
noncomputable instance qAdditive (A : CochainDGAlgebra R) :
    (Q.{u, v} A).Additive := sorry

/-- The derived category carries the `R`-linear structure induced by the DG homotopy
localization.  Naming this specialization prevents downstream APIs from unfolding the Verdier
quotient to find its scalar action. -/
@[stacks 09KX "linearity of the DG derived category"]
noncomputable instance categoryLinear (A : CochainDGAlgebra R) :
    Linear R (Category.{u, v} A) :=
  Localization.linear R (Q A) (Homotopy.acyclic A).trW

/-- The canonical functor from the DG homotopy category to the derived category is
`R`-linear. -/
@[stacks 09KX "linearity of the DG derived localization"]
noncomputable instance qLinear (A : CochainDGAlgebra R) :
    Functor.Linear R (Q.{u, v} A) := sorry

/-- Every shift on the derived category is additive.  This specialized instance keeps
downstream typeclass search from unfolding the Verdier quotient repeatedly. -/
@[stacks 09KX "additivity of shifts in the DG derived category"]
noncomputable instance shiftsAdditive (A : CochainDGAlgebra R) :
    ∀ n : ℤ, (shiftFunctor (Category.{u, v} A) n).Additive :=
  CategoryTheory.ObjectProperty.VerdierQuotient.shiftsAdditive
    (Homotopy.acyclic.{u, v} A)

/-- Every shift on the derived category is `R`-linear.  The construction descends the
corresponding linear shift on the DG homotopy category through the Verdier localization. -/
@[stacks 09KX "linearity of shifts in the DG derived category"]
noncomputable instance shiftsLinear (A : CochainDGAlgebra R) :
    ∀ n : ℤ, Functor.Linear R (shiftFunctor (Category.{u, v} A) n) := sorry

/-- The canonical quotient functor is also a localization at quasi-isomorphisms. -/
@[stacks 09KX]
instance qIsLocalization (A : CochainDGAlgebra R) :
    (Q.{u, v} A).IsLocalization (quasiIso A) := sorry

/-- Definition 22.22.2 (09KX): degree-`n` homology descended to the derived category. -/
@[stacks 09KX]
noncomputable def homologyFunctor (A : CochainDGAlgebra R) (n : ℤ) :
    Category.{u, v} A ⥤ ModuleCat.{v} R :=
  Localization.lift (Homotopy.homologyFunctor A n)
    (Homotopy.Acyclic.trW_isInvertedBy_homologyFunctor A n) (Q A)

/-- Derived homology is additive. -/
@[stacks 09KX "additivity of derived homology"]
noncomputable instance homologyFunctorAdditive (A : CochainDGAlgebra R) (n : ℤ) :
    (homologyFunctor.{u, v} A n).Additive := sorry

/-- Derived homology is `R`-linear. -/
@[stacks 09KX "linearity of derived homology"]
noncomputable instance homologyFunctorLinear (A : CochainDGAlgebra R) (n : ℤ) :
    Functor.Linear R (homologyFunctor.{u, v} A n) := sorry

/-- Composing derived homology with the quotient functor recovers homology on the homotopy
category. -/
@[stacks 09KX "factorization of homology through the DG derived category"]
noncomputable def homologyFunctorFactors (A : CochainDGAlgebra R) (n : ℤ) :
    Q.{u, v} A ⋙ homologyFunctor A n ≅ Homotopy.homologyFunctor A n :=
  Localization.fac (Homotopy.homologyFunctor A n)
    (Homotopy.Acyclic.trW_isInvertedBy_homologyFunctor A n) (Q A)

/-- Derived homology is a lift of homology on the homotopy category along the localization
`Q A`, witnessed by the canonical factorization `homologyFunctorFactors`.  Mathlib's generic
`Localization.liftingLift` does not unfold the named definition `homologyFunctor`, so this
specialization is stated explicitly. -/
@[stacks 09KX "derived homology lifts homology"]
noncomputable instance homologyFunctorLifting (A : CochainDGAlgebra R) (n : ℤ) :
    Localization.Lifting (Q A) (Homotopy.acyclic.{u, v} A).trW
      (Homotopy.homologyFunctor A n) (homologyFunctor A n) :=
  ⟨homologyFunctorFactors A n⟩

/-- A functor from the derived category that recovers homology after localization is
canonically isomorphic to the descended homology functor: the comparison is the unique lift,
along the localization `Q A`, of the given identification on the homotopy category. -/
@[stacks 09KX "uniqueness of descended derived homology"]
noncomputable def homologyFunctorUniqueIso (A : CochainDGAlgebra R) (n : ℤ)
    (F : Category.{u, v} A ⥤ ModuleCat.{v} R)
    (e : Q A ⋙ F ≅ Homotopy.homologyFunctor A n) :
    F ≅ homologyFunctor A n :=
  Localization.liftNatIso (Q A) (Homotopy.acyclic.{u, v} A).trW
    (Q A ⋙ F) (Homotopy.homologyFunctor A n) F (homologyFunctor A n) e

/-- On objects coming from the homotopy category, the uniqueness comparison is the given
identification followed by the inverse of the canonical factorization of derived homology. -/
@[stacks 09KX "uniqueness comparison on localized objects"]
theorem homologyFunctorUniqueIso_hom_app (A : CochainDGAlgebra R) (n : ℤ)
    (F : Category.{u, v} A ⥤ ModuleCat.{v} R)
    (e : Q A ⋙ F ≅ Homotopy.homologyFunctor A n)
    (X : K R (DifferentialGradedModule.{u, v} A)) :
    (homologyFunctorUniqueIso A n F e).hom.app ((Q A).obj X) =
      e.hom.app X ≫ (homologyFunctorFactors A n).inv.app X := sorry

end Derived

end DifferentialGradedModule
