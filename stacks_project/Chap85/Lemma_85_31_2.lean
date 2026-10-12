/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import stacks_project.Chap85.Definition_85_27_1_Cartesian
public import stacks_project.Chap85.Definition_85_27_3_Nerve
public import stacks_project.Chap85.Lemma_85_31_2_RelatedPoints
public import ReasLib.AlgebraicGeometry.SimplicialScheme.RelatedPoints
import StacksCheckRecall

/-!
# Quasi-compactness of related points

If `f : X ⟶ S` is quasi-compact and `π : Y ⟶ f.simplicialScheme` is cartesian,
then `relatedPoints y` is a quasi-compact subset of `Y _⦋0⦌`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Simplicial

universe u

namespace AlgebraicGeometry

/- Lemma 85.31.2: if `f : X ⟶ S` is a quasi-compact morphism of schemes and
`π : Y ⟶ f.simplicialScheme` is a cartesian morphism of simplicial schemes,
then for every point `y` of `Y _⦋0⦌` the set `relatedPoints y` of points `y'`
of `Y _⦋0⦌` for which some `y1` of `Y _⦋1⦌` satisfies `Y.δ 1 y1 = y` and
`Y.δ 0 y1 = y'` is a quasi-compact subset of `Y _⦋0⦌`. -/
@[stacks 024H]
#check (AlgebraicGeometry.isCompact_relatedPoints :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (Y : SimplicialObject Scheme.{u}) (π : Y ⟶ f.simplicialScheme)
    [SimplicialObject.IsCartesian π] (y : Y _⦋0⦌),
    IsCompact (AlgebraicGeometry.relatedPoints y))

end AlgebraicGeometry
