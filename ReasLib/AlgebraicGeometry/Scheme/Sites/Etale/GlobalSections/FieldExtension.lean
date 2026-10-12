/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Base change along a field extension of a separably closed field induces a bijection
on global sections of every set-valued sheaf on the small étale site. -/
theorem restrictGlobalSection_bijective_baseChange_of_isSepClosed
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed k]
    {S : Scheme.{u}} (σ : S ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective (AlgebraicGeometry.Scheme.Etale.restrictGlobalSection
      (AlgebraicGeometry.FieldExtension.toSource k K σ) F) := sorry

end AlgebraicGeometry.Scheme.Etale
