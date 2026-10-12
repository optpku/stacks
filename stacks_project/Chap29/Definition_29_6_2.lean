/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage
import StacksCheckRecall

/-!
# Definition 29.6.2

The scheme-theoretic image is the smallest closed subscheme through which a morphism factors.

@stack 01R7
-/

@[expose] public section

open CategoryTheory

universe u

/- Definition 29.6.2: The canonical scheme-theoretic image is the smallest closed
subscheme through which the morphism factors. -/
@[stacks 01R7] #check
  (AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticImageFactorization_image :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      AlgebraicGeometry.IsSchemeTheoreticImageFactorization f f.toImage f.imageι)
