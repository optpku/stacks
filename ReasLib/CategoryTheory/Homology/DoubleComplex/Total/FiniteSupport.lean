/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite support on total-complex fibres

This leaf isolates the only support hypothesis needed to replace a coproduct indexed by a total
degree with a finite coproduct.  It is shape-polymorphic: the cohomological antidiagonal predicate
used by spectral sequences is a specialization in `DoubleComplex.TotalSupport`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe u v u' v' w₁ w₂ w

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I : Type w}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I}
variable [TotalComplexShape c₁ c₂ c]

namespace Total.Support

/-- Every fibre of the total-degree map contains only finitely many nonzero bidegrees.

The predicate records pairs of indices rather than choosing a section of the total-degree map.
This makes it applicable to arbitrary complex shapes, including shapes where a total degree does
not determine one coordinate from the other.
-/
@[stacks 0132 "finite support on total-complex fibres"]
def Finite (K : HomologicalComplex₂ C c₁ c₂) : Prop :=
  ∀ n : I,
    {ij : I₁ × I₂ |
      ComplexShape.π c₁ c₂ c ij = n ∧ ¬ IsZero ((K.X ij.1).X ij.2)}.Finite

namespace Finite

variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

/-- A zero-morphism-preserving functor transports finite total-degree support. -/
@[stacks 0132 "functoriality of finite total support"]
theorem map {K : HomologicalComplex₂ C c₁ c₂}
    (hfin : Total.Support.Finite (c := c) K)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    Total.Support.Finite (c := c)
      ((F.mapHomologicalComplex₂ c₁ c₂).obj K) := sorry

end Finite

section Totalization

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I : Type w}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I}
variable [TotalComplexShape c₁ c₂ c]

/-- Finite total-degree support is sufficient for totalization in a category with finite
coproducts. -/
@[stacks 0132 "finite support gives a total complex"]
theorem Finite.hasTotal [HasFiniteCoproducts C]
    {K : HomologicalComplex₂ C c₁ c₂}
    (hfin : Total.Support.Finite (c := c) K) :
    K.HasTotal c := sorry

end Totalization

namespace Finite

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I : Type w}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I}
variable [TotalComplexShape c₁ c₂ c]

/-- A finite-support total has injective terms whenever all of its bidegree terms are injective.

This is the shape-polymorphic owner; cohomological double complexes use it through the
`AntidiagonalSupport.Finite` facade.
-/
@[stacks 0132 "injectivity of a finite-support total"]
theorem injective [DecidableEq I]
    {K : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c]
    (hfin : Total.Support.Finite (c := c) K)
    (hinj : ∀ i₁ i₂, Injective ((K.X i₁).X i₂)) (n : I) :
    Injective ((K.total c).X n) := sorry

end Finite

end Total.Support

end HomologicalComplex₂
