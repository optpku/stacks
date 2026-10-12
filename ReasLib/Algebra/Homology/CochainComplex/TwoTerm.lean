/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Double
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Two-term cochain complexes

This file specializes `HomologicalComplex.double` to cochain complexes supported in degrees
`-1` and `0`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The cochain complex consisting of a morphism in degrees `-1` and `0`. -/
noncomputable abbrev twoTerm {N M : C} (d : N ⟶ M) : CochainComplex C ℤ :=
  HomologicalComplex.double d (ComplexShape.up_mk (-1) 0 (neg_add_cancel 1))

/-- The degree `-1` term of a two-term cochain complex is its source. -/
noncomputable def twoTermXNegOneIso {N M : C} (d : N ⟶ M) :
    (twoTerm d).X (-1) ≅ N :=
  HomologicalComplex.doubleXIso₀ d (ComplexShape.up_mk (-1) 0 (neg_add_cancel 1))

/-- The degree `0` term of a two-term cochain complex is its target. -/
noncomputable def twoTermXZeroIso {N M : C} (d : N ⟶ M) :
    (twoTerm d).X 0 ≅ M :=
  HomologicalComplex.doubleXIso₁ d (ComplexShape.up_mk (-1) 0 (neg_add_cancel 1))
    (neg_ne_zero.mpr one_ne_zero)

/-- A two-term cochain complex vanishes below degree `-1`. -/
instance twoTermIsStrictlyGE {N M : C} (d : N ⟶ M) : (twoTerm d).IsStrictlyGE (-1) :=
  by sorry

/-- A two-term cochain complex vanishes above degree `0`. -/
instance twoTermIsStrictlyLE {N M : C} (d : N ⟶ M) : (twoTerm d).IsStrictlyLE 0 :=
  by sorry

variable {R : Type u} [Ring R] {N M : ModuleCat.{v} R}

/-- Freeness of the source of a two-term complex transfers to its degree `-1` term. -/
instance twoTermXNegOneFree (d : N ⟶ M) [Module.Free R N] :
    Module.Free R ((twoTerm d).X (-1)) :=
  Module.Free.of_equiv (twoTermXNegOneIso d).symm.toLinearEquiv

/-- Finiteness of the source of a two-term complex transfers to its degree `-1` term. -/
instance twoTermXNegOneFinite (d : N ⟶ M) [Module.Finite R N] :
    Module.Finite R ((twoTerm d).X (-1)) :=
  Module.Finite.equiv (twoTermXNegOneIso d).symm.toLinearEquiv

/-- Freeness of the target of a two-term complex transfers to its degree `0` term. -/
instance twoTermXZeroFree (d : N ⟶ M) [Module.Free R M] :
    Module.Free R ((twoTerm d).X 0) :=
  Module.Free.of_equiv (twoTermXZeroIso d).symm.toLinearEquiv

/-- Finiteness of the target of a two-term complex transfers to its degree `0` term. -/
instance twoTermXZeroFinite (d : N ⟶ M) [Module.Finite R M] :
    Module.Finite R ((twoTerm d).X 0) :=
  Module.Finite.equiv (twoTermXZeroIso d).symm.toLinearEquiv

/-- The differential of a two-term cochain complex is its defining morphism under the endpoint
identifications. -/
@[simp]
theorem twoTerm_d {N M : C} (d : N ⟶ M) :
    (twoTerm d).d (-1) 0 = (twoTermXNegOneIso d).hom ≫ d ≫ (twoTermXZeroIso d).inv := sorry

end CochainComplex

end
