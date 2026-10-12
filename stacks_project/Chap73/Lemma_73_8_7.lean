/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap73.Lemma_73_8_7_Equalizer
public import stacks_project.Chap73.Lemma_73_8_8_Site

/-!
# Characterization of sheaves on the big ph site of an algebraic space

A presheaf on `(Spaces/X)_ph` is a sheaf if and only if it satisfies the sheaf
condition for étale coverings and the proper-surjective equalizer condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace
namespace Ph
namespace Sheaf

/-- Lemma 73.8.7: let `S` be a scheme, let `X` be an algebraic space over `S`,
and let `F` be a presheaf on `(Spaces/X)_ph`. Then `F` is a sheaf if and only
if `F` satisfies the sheaf condition for étale coverings, and if
`f : V ⟶ U` is a proper surjective morphism of `(Spaces/X)_ph`, then `F(U)`
maps bijectively to the equalizer of the two maps `F(V) ⟶ F(V ×_U V)`. -/
@[stacks 0DFM]
theorem iffEtaleAndEqualizer {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : (Over X)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (bigPhSite X) F ↔
      Presheaf.IsSheaf
          ((etalePrecoverage : Precoverage (AlgebraicSpace S)).toGrothendieck.over X) F ∧
        Equalizer.IsProperSurjective F :=
  sorry

end Sheaf
end Ph
end AlgebraicGeometry.AlgebraicSpace
