module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine.Ample
import StacksCheckRecall

/-!
# Lemma 71.14.7

A morphism of algebraic spaces is quasi-affine if and only if its
structure sheaf is relatively ample.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory

universe u

/- Lemma 71.14.7: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Then `f` is quasi-affine if and only if `𝒪_X` is `f`-relatively
ample. -/
@[stacks 0GUQ] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiAffine_iff_structureSheaf_relativelyAmple :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      QuasiAffine f ↔
        RelativelyAmple f (SheafOfModules.unit (structureSheaf X) : X.Modules))
