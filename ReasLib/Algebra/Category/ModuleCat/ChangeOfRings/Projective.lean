/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective objects under extension of scalars

Extension of scalars is a left adjoint whose right adjoint preserves
epimorphisms, hence it preserves projective objects.  The canonical instance
belongs here rather than in any derived or chapter-specific construction.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat.ExtendScalars

/-- Extension of scalars preserves projective objects for every map of
commutative rings. -/
@[stacks 00M8 "extension-of-scalars projectives"]
instance preservesProjectiveObjects
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} f).PreservesProjectiveObjects := by
  letI : (ModuleCat.restrictScalars.{u, u, u} f).PreservesEpimorphisms :=
    { preserves := fun g hg ↦ by
        rw [ModuleCat.epi_iff_surjective] at hg ⊢
        exact hg }
  exact Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj.{0, u, u} f)

end ModuleCat.ExtendScalars
