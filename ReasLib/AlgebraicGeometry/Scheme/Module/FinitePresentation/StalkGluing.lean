/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Gluing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing

/-!
# Gluing finitely presented modules over a stalk

This leaf records the categorical gluing equivalence for finitely presented modules over the
complement of a closed point and the local scheme at that point.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Finitely presented modules on a scheme are equivalent to compatible finitely presented
modules on the complement of a closed point and on the local scheme at that point. -/
theorem finitePresentationModules_equivalence_stalkGluing
    (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
    (s : S) (hs : s ∈ closedPoints S)
    (hU : (U : Set S) = ({s} : Set S)ᶜ) :
    Nonempty
      (FinitePresentationModules S ≌
        finitePresentationModuleGluingCategory U (stalkOpenIntersection S U s)
          ((S.fromSpecStalk s) ∣_ U)) := sorry

end AlgebraicGeometry
