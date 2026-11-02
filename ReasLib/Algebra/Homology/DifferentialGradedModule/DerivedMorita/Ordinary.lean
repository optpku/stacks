/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Regular.End
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Concentrated
public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero.HomologyZero
public import ReasLib.CategoryTheory.Pretriangulated.Tilting.Equivalence
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Derived Morita Equivalence with an Algebra Concentrated in Degree Zero

This leaf gives the intrinsic DG-derived-category form of the tilting-object characterization.
Unlike a statement about arbitrary triangulated categories, the converse remains in the enhanced
category `DifferentialGradedModule.Derived.Category B`, where the endomorphism DGA construction
and quasi-isomorphism comparison are available.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe uR vA vB v w

namespace CochainDGAlgebra.DerivedMorita

variable {R : Type uR} [CommRing R]

/-- A tilting object for `A` is a compact weak generator whose shifted endomorphisms vanish away
from degree zero and whose endomorphism algebra is identified with that of the regular
`A`-object. -/
@[stacks 09S8 "tilting object for a differential graded algebra"]
abbrev IsTiltingFor {B : CochainDGAlgebra.{uR, vB} R}
    (A : CochainDGAlgebra.{uR, vA} R)
    (P : DifferentialGradedModule.Derived.Category.{uR, vB} B) : Prop :=
  CategoryTheory.IsTiltingFor (R := R) (E := A.homologyZero) P

/-- The defining compactness, generation, self-extension, and endomorphism-algebra conditions
for a tilting object. -/
@[stacks 09S8 "defining conditions for a differential graded tilting object"]
theorem isTiltingFor_iff {B : CochainDGAlgebra.{uR, vB} R}
    (A : CochainDGAlgebra.{uR, vA} R)
    (P : DifferentialGradedModule.Derived.Category.{uR, vB} B) :
    IsTiltingFor A P ↔
      IsCompactObject P ∧
        IsWeakGenerator P ∧
        (∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0) ∧
        Nonempty (End P ≃ₐ[R] A.homologyZero) := sorry

/-- A chosen ordinary algebra model for the endomorphisms of the regular object rewrites the
canonical tilting criterion without exposing that derived-category implementation detail.  This
is the bridge to source statements using a degree-zero algebra such as `H⁰(A)`; the bridge itself
must be supplied by the relevant homology model. -/
@[stacks 09S8 "tilting criterion through a chosen degree-zero endomorphism model"]
theorem isTiltingFor_iff_of_endEquiv
    {A : CochainDGAlgebra.{uR, vA} R}
    {B : CochainDGAlgebra.{uR, vB} R}
    {E : Type w} [Ring E] [Algebra R E]
    (P : DifferentialGradedModule.Derived.Category.{uR, vB} B)
    (hE : Nonempty (A.homologyZero ≃ₐ[R] E)) :
    IsTiltingFor A P ↔
      IsCompactObject P ∧
        IsWeakGenerator P ∧
        (∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0) ∧
        Nonempty (End P ≃ₐ[R] E) := sorry

/-- The generic tilting criterion can also be written using the ordinary endomorphism algebra of
the regular derived object, via the canonical `H⁰(A)` comparison. -/
@[stacks 09S8 "tilting criterion through regular derived endomorphisms"]
theorem isTiltingFor_iff_regularEnd
    {A : CochainDGAlgebra.{uR, vA} R}
    {B : CochainDGAlgebra.{uR, vB} R}
    (P : DifferentialGradedModule.Derived.Category.{uR, vB} B) :
    IsTiltingFor A P ↔
      IsCompactObject P ∧
        IsWeakGenerator P ∧
        (∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0) ∧
        Nonempty (End P ≃ₐ[R]
          End (DifferentialGradedModule.Derived.regularObject A)) := sorry

/-- A tilting object is compact. -/
@[stacks 09S8 "compactness of a differential graded tilting object"]
theorem IsTiltingFor.isCompact
    {A : CochainDGAlgebra.{uR, vA} R} {B : CochainDGAlgebra.{uR, vB} R}
    {P : DifferentialGradedModule.Derived.Category.{uR, vB} B}
    (hP : IsTiltingFor A P) :
    IsCompactObject P := sorry

/-- A tilting object weakly generates its derived category. -/
@[stacks 09S8 "generation by a differential graded tilting object"]
theorem IsTiltingFor.isWeakGenerator
    {A : CochainDGAlgebra.{uR, vA} R} {B : CochainDGAlgebra.{uR, vB} R}
    {P : DifferentialGradedModule.Derived.Category.{uR, vB} B}
    (hP : IsTiltingFor A P) :
    IsWeakGenerator P := sorry

/-- A DG tilting object is self-orthogonal. -/
@[stacks 09S8 "self-orthogonality of a differential graded tilting object"]
theorem IsTiltingFor.isSelfOrthogonal
    {A : CochainDGAlgebra.{uR, vA} R} {B : CochainDGAlgebra.{uR, vB} R}
    {P : DifferentialGradedModule.Derived.Category.{uR, vB} B}
    (hP : IsTiltingFor A P) :
    CategoryTheory.IsSelfOrthogonal P := sorry

/-- A tilting object has no nonzero-degree self-extensions. -/
@[stacks 09S8 "vanishing of nonzero-degree tilting self-extensions"]
theorem IsTiltingFor.selfExt_eq_zero
    {A : CochainDGAlgebra.{uR, vA} R} {B : CochainDGAlgebra.{uR, vB} R}
    {P : DifferentialGradedModule.Derived.Category.{uR, vB} B}
    (hP : IsTiltingFor A P) (i : ℤ) (hi : i ≠ 0)
    (f : P ⟶ P⟦i⟧) :
    f = 0 := sorry

/-- A tilting object's endomorphism algebra is identified with the canonical degree-zero
cohomology algebra of the source DGA. -/
@[stacks 09S8 "endomorphism algebra of a differential graded tilting object"]
theorem IsTiltingFor.nonempty_endEquiv
    {A : CochainDGAlgebra.{uR, vA} R} {B : CochainDGAlgebra.{uR, vB} R}
    {P : DifferentialGradedModule.Derived.Category.{uR, vB} B}
    (hP : IsTiltingFor A P) :
    Nonempty (End P ≃ₐ[R] A.homologyZero) := sorry

/-- A tilting object's endomorphism algebra can also be compared with the ordinary endomorphisms
of the regular derived object through the canonical regular-end comparison. -/
@[stacks 09S8 "tilting endomorphisms compared with the regular derived object"]
theorem IsTiltingFor.nonempty_regularEndEquiv
    {A : CochainDGAlgebra.{uR, vA} R} {B : CochainDGAlgebra.{uR, vB} R}
    {P : DifferentialGradedModule.Derived.Category.{uR, vB} B}
    (hP : IsTiltingFor A P) :
    Nonempty (End P ≃ₐ[R]
      End (DifferentialGradedModule.Derived.regularObject A)) := sorry

/-- Lemma 22.37.4 (1) (09S8): if `A` is concentrated in degree zero, then its canonical derived
category is `R`-linearly triangulated-equivalent to `D(B)` exactly when `D(B)` contains a compact
weak generator with no nonzero-degree self-extensions and with degree-zero endomorphism algebra
identified with that of the regular `A`-object. -/
@[stacks 09S8]
theorem nonempty_equivalence_iff_exists_tilting
    (A : CochainDGAlgebra.{uR, v} R) (B : CochainDGAlgebra.{uR, v} R)
    (hA : A.IsConcentratedInDegreeZero) :
    Nonempty (RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category.{uR, v} A)
      (DifferentialGradedModule.Derived.Category.{uR, v} B)) ↔
      ∃ P : DifferentialGradedModule.Derived.Category.{uR, v} B,
        IsTiltingFor A P := sorry

/-- Lemma 22.37.4 (2) (09S8): the equivalence constructed from a compact generator with the
prescribed self-extensions sends the regular `A`-object to that generator. -/
@[stacks 09S8 "the derived Morita equivalence sends the regular object to the generator"]
theorem exists_equivalence_obj_regular
    (A : CochainDGAlgebra.{uR, v} R) (B : CochainDGAlgebra.{uR, v} R)
    (hA : A.IsConcentratedInDegreeZero)
    (P : DifferentialGradedModule.Derived.Category.{uR, v} B)
    (hP : IsTiltingFor A P) :
    ∃ e : RLinear.TriangulatedEquivalence R
        (DifferentialGradedModule.Derived.Category.{uR, v} A)
        (DifferentialGradedModule.Derived.Category.{uR, v} B),
      Nonempty (e.functor.obj (DifferentialGradedModule.Derived.regularObject A) ≅ P) := sorry

end CochainDGAlgebra.DerivedMorita
