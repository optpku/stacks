/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf

/-!
# Local surjectivity for quotient sheaves of algebraic-space pre-relations

Equality in a quotient sheaf is witnessed by relation points on an fppf covering.
The relation therefore maps locally surjectively onto the quotient-map kernel pair.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- Two scheme-valued points have equal quotient-sheaf classes for a pre-equivalence
relation exactly when an fppf covering carries relation points whose source and target
are the restricted points. -/
theorem quotientClass_eq_iff_exists_cover {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) (hP : P.IsPreEquivalence) {T : Over S}
    (a b : U.left.functorOfPoints.obj (op T)) :
    P.quotientClass T a = P.quotientClass T b ↔
      ∃ cover : Precoverage.ZeroHypercover.{u + 1}
          (Scheme.fppfPrecoverage.comap (Over.forget S)) T,
        ∀ index : cover.I₀,
          ∃ relationPoint : P.left.left.functorOfPoints.obj (op (cover.X index)),
            U.left.functorOfPoints.map (cover.f index).op a =
                P.s.left.app (op (cover.X index)) relationPoint ∧
              U.left.functorOfPoints.map (cover.f index).op b =
                P.t.left.app (op (cover.X index)) relationPoint := sorry

/-- For a pre-equivalence relation, the canonical morphism of fppf sheaves from the
relation to the kernel pair of the quotient map is locally surjective. -/
theorem relationToKernelPair_locallySurjective {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) (hP : P.IsPreEquivalence) :
    Sheaf.IsLocallySurjective P.relationToKernelPair := sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
