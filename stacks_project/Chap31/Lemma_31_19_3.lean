/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Map.Affine

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

universe u

/- Lemma 31.19.3: a commutative square whose immersion sides are i and i' has a unique
graded conormal-algebra comparison with the canonical degreewise associated-graded formula. -/
@[stacks 0634] #check
  (AlgebraicGeometry.Scheme.ConormalAlgebra.existsUnique_map :
    ∀ {Z X Z' X' : AlgebraicGeometry.Scheme.{u}}
      {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
      [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.IsImmersion i'],
      (sq : CommSq f i i' g) →
        ∃! tau : GradedAlgebraSheaf.Hom.{u, u}
          (AlgebraicGeometry.Scheme.Modules.GradedAlgebra.pullback f
            (AlgebraicGeometry.Scheme.ConormalAlgebra i'))
          (AlgebraicGeometry.Scheme.ConormalAlgebra i),
          AlgebraicGeometry.Scheme.ConormalAlgebra.IsAffineMap sq tau)

/- The canonical comparison is available as explicit bundled graded-algebra morphism data. -/
#check
  (AlgebraicGeometry.Scheme.ConormalAlgebra.map :
    ∀ {Z X Z' X' : AlgebraicGeometry.Scheme.{u}}
      {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'},
      CommSq f i i' g →
        GradedAlgebraSheaf.Hom.{u, u}
          (AlgebraicGeometry.Scheme.Modules.GradedAlgebra.pullback f
            (AlgebraicGeometry.Scheme.ConormalAlgebra i'))
          (AlgebraicGeometry.Scheme.ConormalAlgebra i))

/- On compatible affine charts, the comparison is induced by the ambient section-ring map. -/
#check
  (AlgebraicGeometry.Scheme.ConormalAlgebra.map_affine :
    ∀ {Z X Z' X' : AlgebraicGeometry.Scheme.{u}}
      {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
      [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.IsImmersion i'],
      (sq : CommSq f i i' g) →
        AlgebraicGeometry.Scheme.ConormalAlgebra.IsAffineMap sq
          (AlgebraicGeometry.Scheme.ConormalAlgebra.map sq))
