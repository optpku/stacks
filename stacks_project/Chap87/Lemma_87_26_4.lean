/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Monomorphism.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.26.4: monomorphisms of formal algebraic spaces are characterized
by the six base-change and covering tests below.

Approved local erratum to Stacks tag 0GHV: clause (6) tests the projection
X ×_Y Z ⟶ Z, correcting the printed projection to X. The editorial
"add more here" placeholder is not a mathematical clause. -/
@[stacks 0GHV] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.Monomorphisms.tfae :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
      [FormalAlgebraicSpace.IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
      List.TFAE [Mono f,
        FormalAlgebraicSpace.Monomorphisms.forallScheme f,
        FormalAlgebraicSpace.Monomorphisms.forallAffine f,
        FormalAlgebraicSpace.Monomorphisms.existsCoverOnTarget f,
        FormalAlgebraicSpace.Monomorphisms.existsSheafSurjection f,
        FormalAlgebraicSpace.Monomorphisms.existsFppf f])
