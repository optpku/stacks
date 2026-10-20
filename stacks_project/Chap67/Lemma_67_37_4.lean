module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
import StacksCheckRecall

/-!
# Characterizations of smoothness for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

/- Lemma 67.37.4: For a morphism of algebraic spaces over a scheme, smoothness,
pointwise smoothness, the scheme and affine-scheme base-change tests, the
surjective étale target and source cover tests, the universal and existential
étale scheme-square tests, and smoothness on Zariski covers of the target and
its inverse images are equivalent. -/
@[stacks 03ZF] #check (AlgebraicGeometry.AlgebraicSpace.smooth_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ Smooth f
      , ∀ x : Points X, SmoothAt f x
      , Smooth.baseChangeOnSchemes f
      , Smooth.baseChangeOnAffineSchemes f
      , Smooth.existsSurjectiveEtaleTarget f
      , Smooth.existsSurjectiveEtaleSource f
      , Smooth.forallEtaleSquare f
      , Smooth.existsEtaleSquare f
      , Smooth.existsZariskiCover.{u, v} f ])
