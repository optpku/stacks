module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage
import StacksCheckRecall

/-!
# Lemma 29.6.1

The canonical scheme-theoretic image and its universal factorization property.

@stack 01R6
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.6.1: Every morphism of schemes has a least closed subscheme of its target
through which it factors. -/
@[stacks 01R6] #check
  (AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticImageFactorization_image :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      AlgebraicGeometry.IsSchemeTheoreticImageFactorization f f.toImage f.imageι)
