module

public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.QuasiFinite
import StacksCheckRecall

/-!
# Finite morphisms of algebraic spaces are quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.45.8: A finite morphism of algebraic spaces is quasi-finite. -/
@[stacks 04NY] #check (AlgebraicGeometry.AlgebraicSpace.QuasiFinite.of_isFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
    [AlgebraicGeometry.AlgebraicSpace.IsFinite f] →
      AlgebraicGeometry.AlgebraicSpace.QuasiFinite f)
