/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.StandardCover
import StacksCheckRecall

universe u

/- Lemma 30.2.1: the Čech cohomology of a quasi-coherent module on a standard
distinguished-open cover of an affine open vanishes in every positive degree. -/
@[stacks 01X9] #check
  (AlgebraicGeometry.Scheme.StandardZariskiCover.OnAffineOpen.isCechAcyclicFamily :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {U : X.affineOpens}
      (𝒰 : AlgebraicGeometry.Scheme.StandardZariskiCover.OnAffineOpen.{u, u} X U)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ), 0 < p →
        CategoryTheory.Limits.IsZero
          (AlgebraicGeometry.RingedSpace.moduleCechCohomology 𝒰.opens ℱ p))
