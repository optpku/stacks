/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import stacks_project.Chap66.Lemma_66_28_1_Hom

/-!
# Relative differentials of a morphism of algebraic spaces

The sheaf of relative differentials `Ω_{X/Y}` of a morphism of algebraic spaces is the
sheafification of the objectwise Kähler differentials of the inverse-image structure map
`h⁻¹ 𝒪_Y ⟶ 𝒪_X` on the small étale site of `X`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}}

/-- Forgetting commutativity of the commutative structure presheaf recovers `structureSheaf`. -/
theorem structureSheaf_obj_eq_forget_comm (X : AlgebraicSpace S) :
    (structureSheaf X).obj =
      (commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat :=
  structurePresheaf_eq_forget_comm X

/-- View an `𝒪_X`-module as a presheaf of modules over the commutative structure sheaf. -/
def toCommPresheaf {X : AlgebraicSpace S} (M : X.Modules) :
    PresheafOfModules ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat) :=
  cast rfl M.val

/-- The sheaf of relative differentials `Ω_{X/Y}` of a morphism of algebraic spaces, as an
`𝒪_X`-module on the small étale site. -/
def relativeDifferentials {X Y : AlgebraicSpace S} (h : X ⟶ Y) : X.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj
    (relativeDifferentials' (commInverseImageStructureSheafMap h).hom)

/-- The relative-differentials sheaf is the sheafification of the presheaf of Kähler
differentials of `commInverseImageStructureSheafMap h`. -/
theorem relativeDifferentials_spec {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    relativeDifferentials h =
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj
        (relativeDifferentials' (commInverseImageStructureSheafMap h).hom) :=
  rfl

/-- The universal derivation `d_{X/Y}` of a morphism of algebraic spaces, with values in
`relativeDifferentials h`. -/
def universalDerivation {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (toCommPresheaf (relativeDifferentials h)).Derivation'
      (commInverseImageStructureSheafMap h).hom :=
  (derivation' (commInverseImageStructureSheafMap h).hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (structureSheaf X).obj)).unit.app
      (relativeDifferentials' (commInverseImageStructureSheafMap h).hom))

/-- Evaluation of the universal derivation on a local section of `𝒪_X`. -/
theorem universalDerivation_d {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {U : (smallEtaleSite X)ᵒᵖ} (t : (commStructureSheaf X).obj.obj U) :
    (universalDerivation h).d t =
      ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (structureSheaf X).obj)).unit.app
          (relativeDifferentials' (commInverseImageStructureSheafMap h).hom)).app U
        ((derivation' (commInverseImageStructureSheafMap h).hom).d t) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Hom
