/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.ObjectProperty.SiteLocal
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 35.15.1: For any of the fpqc, fppf, syntomic, smooth, étale, or
Zariski precoverages, a property of schemes is local when it holds on a scheme
exactly when it holds on every member of each covering family. -/
@[stacks 0348] #check
  (CategoryTheory.ObjectProperty.IsLocal.iff_forall_zeroHypercover :
    ∀ (P : CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      (K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme.{u}) [K.HasIsos],
      P.IsLocal K ↔
        ∀ ⦃X : AlgebraicGeometry.Scheme.{u}⦄ (𝒰 : K.ZeroHypercover X),
          P X ↔ ∀ i, P (𝒰.X i))

/- The covering-family formulation of locality for an object property. -/
#check CategoryTheory.ObjectProperty.iff_of_zeroHypercover
