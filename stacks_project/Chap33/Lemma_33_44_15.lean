/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Ample

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.44.15: let `k` be a field, let `X` be a proper scheme of dimension `≤ 1` over `k`,
and let `ℒ` be an invertible `𝒪_X`-module. Then `ℒ` is ample if and only if its restriction to
every one-dimensional irreducible component has positive degree. -/
@[stacks 0B5Y] #check
  (AlgebraicGeometry.Scheme.Modules.isAmple_iff_curveDegree_pos_on_oneDimensional_irreducibleComponents :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (hXdim : topologicalKrullDim X.left ≤ 1),
      Scheme.Modules.IsAmple ℒ ↔
        ∀ Z : irreducibleComponents X.left,
          ∀ hZdim : topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1,
            0 < Scheme.Modules.curveDegreeOfInvertible
              (X.left.irreducibleComponentSubschemeι Z ≫ X.hom) hZdim.le
              ((Scheme.Modules.pullback (X.left.irreducibleComponentSubschemeι Z)).obj ℒ))
