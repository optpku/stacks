module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
import ReasLib.AlgebraicGeometry.Scheme.Morphism.GenericallyFinite.DenseOpen

/-!
# Dense Open Restrictions of Birational Morphisms

This module gives finiteness conditions under which a birational morphism is
an isomorphism after restriction to dense open subschemes.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsBirational

/-- A birational morphism between schemes with finitely many irreducible components restricts
to an isomorphism between dense opens if it is locally of finite type with reduced target, or
if it is locally of finite presentation. -/
theorem exists_dense_opens_isIso_resLE
    {X Y : Scheme.{u}}
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (f : X ⟶ Y) [IsBirational f]
    (hfiniteType_or_finitePresentation :
      (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ (U : X.Opens) (V : Y.Opens),
      Dense (U : Set X) ∧ Dense (V : Set Y) ∧ ∃ hUV : U ≤ f ⁻¹ᵁ V, IsIso (f.resLE V U hUV) := sorry

/-- Irreducible schemes related over a base by a suitably finite birational morphism are
birational over that base. -/
theorem birationalOver_of_irreducible
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsBirational f]
    (hf_over : f ≫ (Y ↘ S) = (X ↘ S))
    (hfiniteType_or_finitePresentation :
      (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    AlgebraicGeometry.Scheme.BirationalOver (X ↘ S) (Y ↘ S) := sorry

/-- A birational morphism between schemes with finitely many irreducible components is an
isomorphism over a dense open of the target under the stated finiteness hypotheses. -/
theorem exists_dense_open_isIso_restrict
    {X Y : Scheme.{u}}
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (f : X ⟶ Y) [IsBirational f]
    (hqc_or_sep : QuasiCompact f ∨ IsSeparated f)
    (hfiniteType_or_finitePresentation :
      (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsIso (f ∣_ V) := sorry

end AlgebraicGeometry.IsBirational
