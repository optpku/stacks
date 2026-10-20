module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskisMainTheorem
import StacksCheckRecall

/-!
# Zariski's Main Theorem for quasi-finite separated morphisms

A quasi-finite separated morphism of algebraic spaces factors through its
relative normalization as a quasi-compact open immersion followed by an
integral morphism, and is therefore quasi-affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.52.2: the canonical map to the relative normalization is a
quasi-compact open immersion, its structure morphism is integral, and the
original morphism is quasi-affine. -/
@[stacks 0ABS] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiFinite_separated_normalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiFinite f] [Separated f],
      IsOpenImmersion (Hom.toNormalization f) ∧
        QuasiCompact (Hom.toNormalization f) ∧
        IsIntegralHom (Hom.fromNormalization f) ∧ QuasiAffine f)
