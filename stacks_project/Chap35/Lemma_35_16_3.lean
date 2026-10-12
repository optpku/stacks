/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap35.Lemma_35_15_2
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Locality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.16.3: the property that every quasi-compact open of a scheme has finitely
many irreducible components is local in the fppf topology. -/
@[stacks 0BAL] #check
  (AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens.isLocalFppf :
    CategoryTheory.ObjectProperty.IsLocal
      (fun X : AlgebraicGeometry.Scheme.{u} ↦
        AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X)
      AlgebraicGeometry.Scheme.fppfPrecoverage)
