module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_21_2_QuasiAffine
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple

/-!
# Lemma 71.14.7

A morphism of algebraic spaces is quasi-affine if and only if its
structure sheaf is relatively ample.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.14.7: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Then `f` is quasi-affine if and only if `𝒪_X` is `f`-relatively
ample. -/
@[stacks 0GUQ]
theorem quasiAffine_iff_structureSheaf_relativelyAmple
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    QuasiAffine f ↔
      RelativelyAmple f (SheafOfModules.unit (structureSheaf X) : X.Modules) :=
  sorry

/-- A quasi-affine morphism of algebraic spaces has relatively ample structure
sheaf. -/
instance RelativelyAmple.of_quasiAffine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiAffine f] :
    RelativelyAmple f (SheafOfModules.unit (structureSheaf X) : X.Modules) :=
  sorry

/-- Relative ampleness of the structure sheaf witnesses that a morphism of
algebraic spaces is quasi-affine. -/
instance QuasiAffine.of_relativelyAmple_structureSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [RelativelyAmple f (SheafOfModules.unit (structureSheaf X) : X.Modules)] :
    QuasiAffine f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
