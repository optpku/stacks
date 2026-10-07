module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso.Basic
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Equivalences from Quasi-isomorphisms of Cochain DG Algebras

A quasi-isomorphism of cochain differential graded algebras induces an equivalence on the
canonical derived categories of right differential graded modules. The forward functor is
derived extension of scalars and the inverse functor is derived restriction of scalars.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v

namespace CochainDGAlgebra.Hom.Derived

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}

/-- Derived extension along a quasi-isomorphism of cochain differential graded algebras is an
equivalence. -/
@[stacks 09S6 "derived extension along a DGA quasi-isomorphism"]
theorem extension_isEquivalence (f : A ⟶ B)
    (hf : CochainDGAlgebra.quasiIso f) :
    Functor.IsEquivalence (extension f) := sorry

/-- Derived restriction along a quasi-isomorphism of differential graded algebras is an
equivalence. -/
@[stacks 09S6 "derived restriction along a DGA quasi-isomorphism"]
theorem restriction_isEquivalence (f : A ⟶ B)
    (hf : CochainDGAlgebra.quasiIso f) :
    Functor.IsEquivalence (restriction f) := sorry

/-- The unit component of derived extension and restriction along a DGA quasi-isomorphism is
invertible. -/
@[stacks 09S6 "invertible unit of derived DGA restriction"]
theorem unit_app_isIso (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f)
    (X : DifferentialGradedModule.Derived.Category A) :
    IsIso ((adjunction f).unit.app X) := sorry

/-- The counit component of derived extension and restriction along a DGA quasi-isomorphism is
invertible. -/
@[stacks 09S6 "invertible counit of derived DGA restriction"]
theorem counit_app_isIso (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f)
    (Y : DifferentialGradedModule.Derived.Category B) :
    IsIso ((adjunction f).counit.app Y) := sorry

/-- The canonical derived equivalence induced by a DGA quasi-isomorphism, with forward functor
given by derived extension of scalars. -/
@[stacks 09S6 "derived equivalence induced by a DGA quasi-isomorphism"]
noncomputable def equivalence (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f) :
    DifferentialGradedModule.Derived.Category A ≌
      DifferentialGradedModule.Derived.Category B :=
  @Adjunction.toEquivalence _ _ _ _ _ _ (adjunction f)
    (fun X ↦ unit_app_isIso f hf X)
    (fun Y ↦ counit_app_isIso f hf Y)

/-- The forward functor of the canonical equivalence is derived extension of scalars. -/
@[stacks 09S6 "forward functor of the derived DGA equivalence"]
theorem equivalence_functor (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f) :
    (equivalence f hf).functor = extension f := sorry

/-- The inverse functor of the canonical equivalence is derived restriction of scalars. -/
@[stacks 09S6 "inverse functor of the derived DGA equivalence"]
theorem equivalence_inverse (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f) :
    (equivalence f hf).inverse = restriction f := sorry

/-- A quasi-isomorphism of cochain DG algebras induces the canonical `R`-linear triangulated
equivalence whose two functors are derived extension and derived restriction of scalars. -/
@[stacks 09S6 "linear triangulated equivalence induced by a DGA quasi-isomorphism"]
noncomputable def triangulatedEquivalence
    (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f) :
    RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category A)
      (DifferentialGradedModule.Derived.Category B) :=
  RLinear.TriangulatedEquivalence.ofAdjunction R
    (adjunction f) (extension_isEquivalence f hf)

/-- The forward functor of the induced linear triangulated equivalence is derived extension of
scalars. -/
@[stacks 09S6 "forward functor of the linear derived DGA equivalence"]
theorem triangulatedEquivalence_functor
    (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f) :
    (triangulatedEquivalence f hf).functor = extension f := sorry

/-- The inverse functor of the induced linear triangulated equivalence is derived restriction of
scalars. -/
@[stacks 09S6 "inverse functor of the linear derived DGA equivalence"]
theorem triangulatedEquivalence_inverse
    (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f) :
    (triangulatedEquivalence f hf).inverse = restriction f := sorry

end CochainDGAlgebra.Hom.Derived
