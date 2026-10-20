/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Sections
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.44.13: an invertible module of nonpositive degree on every irreducible component of
a proper, reduced, connected, equidimensional one-dimensional scheme over a field has either
trivial global sections or is isomorphic to the structure module. -/
@[stacks 0E22] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree.subsingleton_sections_or_isoUnit_of_components_nonpos :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [IsReduced X.left]
      [ConnectedSpace X.left] (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (hcompdim : ∀ Z : irreducibleComponents X.left,
        topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1),
      (∀ Z : irreducibleComponents X.left,
        Scheme.Modules.curveDegreeOfInvertible
          (X.left.irreducibleComponentSubschemeι Z ≫ X.hom)
          (hcompdim Z).le
          ((Scheme.Modules.pullback (X.left.irreducibleComponentSubschemeι Z)).obj ℒ) ≤ 0) →
      Subsingleton ℒ.sections ∨
        Nonempty (ℒ ≅ (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)))
