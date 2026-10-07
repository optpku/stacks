module

public import stacks_project.Chap75.Lemma_75_28_3_QuasiAffine
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.28.3: an affine or quasi-affine morphism of algebraic spaces over a
scheme transfers the resolution property from a quasi-compact quasi-separated
target to the source. -/
@[stacks 0GUU] #check
  (AlgebraicGeometry.AlgebraicSpace.hasResolutionProperty_of_quasiAffine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.QuasiAffine f]
      [AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact Y]
      [AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated Y],
      AlgebraicGeometry.AlgebraicSpace.HasResolutionProperty Y →
        AlgebraicGeometry.AlgebraicSpace.HasResolutionProperty X)

/- The affine special case. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.hasResolutionProperty_of_affine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Affine f]
      [AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact Y]
      [AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated Y],
      AlgebraicGeometry.AlgebraicSpace.HasResolutionProperty Y →
        AlgebraicGeometry.AlgebraicSpace.HasResolutionProperty X)
