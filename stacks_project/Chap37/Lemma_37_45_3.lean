/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Stratification
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.45.3: a flat, locally finitely presented, separated, locally quasi-finite scheme
morphism with universally bounded fibres admits a finite closed degree stratification whose
rank strata universally classify finite locally free base changes. -/
@[stacks 07RY] #check
  (AlgebraicGeometry.Scheme.Hom.exists_degreeStratification :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.IsSeparated f] [AlgebraicGeometry.LocallyQuasiFinite f],
      AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres f →
        Nonempty (AlgebraicGeometry.Scheme.Hom.DegreeStratification f))
