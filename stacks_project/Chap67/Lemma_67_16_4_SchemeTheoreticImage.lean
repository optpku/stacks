module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.Reduced
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Scheme-theoretic images of reduced algebraic spaces

If `X` is reduced, a scheme-theoretic image factorization of `f : X ⟶ Y` is
the reduced induced algebraic space structure on the closure of the set of
points `|f|(|X|)`. Formation of this image commutes with étale base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.pullbackToImage :
    ∀ {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
      (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y)
      [HasPullback f φ] [HasPullback ι φ], pullback f φ ⟶ pullback ι φ)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.pullbackToInverseImage :
    ∀ {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
      (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [IsSchemeTheoreticImage f toImage ι] [IsClosedImmersion ι] (φ : V ⟶ Y)
      [HasPullback f φ], pullback f φ ⟶ inverseImage φ ι)

end AlgebraicGeometry.AlgebraicSpace
