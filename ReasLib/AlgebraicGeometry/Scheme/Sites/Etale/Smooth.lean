/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous

/-!
# Etale refinements of smooth covers

This leaf compares the big etale and smooth selected-cover sites over a
scheme.  It keeps topology comparison separate from selected-family
refinement and from the counterexample to reverse continuity.
-/

@[expose] public section

open CategoryTheory SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The big etale Grothendieck topology over `S` is bounded above by the big smooth topology. -/
theorem overTopology_le_smooth (S : Scheme.{u}) :
    S.overGrothendieckTopology @Etale ≤ S.overGrothendieckTopology @Smooth := sorry

/-- Example 7.22.5 (0H6Z) (1): every selected smooth cover over `S` has a selected etale
refinement. -/
@[stacks 0H6Z "(1)"]
theorem smoothCover_refinedByEtale
    {S : Scheme.{u}} {X : Over S} (𝒰 : SemiRepresentableFamily.Over.{u} X)
    (h𝒰 : IsCovering ((Scheme.precoverage @Smooth).comap (Over.forget S)) 𝒰) :
    ∃ 𝒱 : SemiRepresentableFamily.Over.{u} X,
      IsCovering (Scheme.etalePrecoverage.comap (Over.forget S)) 𝒱 ∧ Refines 𝒱 𝒰 := sorry

/-- Some selected smooth cover is not itself a selected etale cover. -/
theorem exists_smoothCover_not_covering :
    ∃ (S : Scheme.{u}) (X : Over S) (𝒰 : SemiRepresentableFamily.Over.{u} X),
      IsCovering ((Scheme.precoverage @Smooth).comap (Over.forget S)) 𝒰 ∧
        ¬ IsCovering (Scheme.etalePrecoverage.comap (Over.forget S)) 𝒰 := sorry

/-- Example 7.22.5 (0H6Z) (2): for some base scheme the identity from the big smooth selected
site to the big etale selected site is not continuous. -/
@[stacks 0H6Z "(2)"]
theorem exists_smoothToEtale_not_continuous :
    ∃ S : Scheme.{u},
      ¬ Functor.Precoverage.IsContinuous (𝟭 (Over S))
        ((Scheme.precoverage @Smooth).comap (Over.forget S))
        (Scheme.etalePrecoverage.comap (Over.forget S)) := sorry

end AlgebraicGeometry.Scheme.Etale
