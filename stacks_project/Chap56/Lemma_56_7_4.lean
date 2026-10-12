/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 56.7.4 -/
@[stacks 0FZM] #check
  (AlgebraicGeometry.IsFinite.of_coherent_fullSupport :
    ∀ {V X : AlgebraicGeometry.Scheme.{u}} (f : V ⟶ X)
      [AlgebraicGeometry.IsNoetherian V] [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.Scheme.Hom.QuasiFinite f]
      [AlgebraicGeometry.IsSeparated f] (K : V.Modules) [K.IsCoherent]
      (h_support : AlgebraicGeometry.Scheme.Modules.moduleSupport K = Set.univ)
      [((AlgebraicGeometry.Scheme.Modules.pushforward f).obj K).IsCoherent]
      (hR : ∀ q : ℕ, 0 < q →
        IsZero (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom K q)),
      AlgebraicGeometry.IsFinite f)
