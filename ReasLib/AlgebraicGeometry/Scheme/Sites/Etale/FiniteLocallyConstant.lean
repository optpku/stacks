/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A set-valued sheaf on the small étale site of a scheme is finite locally
constant exactly when it is isomorphic to the sheafified representable of an
étale scheme whose structure morphism is finite. -/
theorem finiteLocallyConstant_iff_exists_finiteEtale
    (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Sheaf.IsFiniteLocallyConstant F ↔
      ∃ (U : X.Etale), IsFinite U.hom ∧
        Nonempty (F ≅ X.smallEtaleTopology.sheafifiedRepresentable U) := sorry

end AlgebraicGeometry.Scheme
