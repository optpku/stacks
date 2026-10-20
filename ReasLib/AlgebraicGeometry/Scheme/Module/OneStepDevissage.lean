/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberSupportDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# One-step dévissages

This module packages the affine diagram and module occurring in a one-step
dévissage over a point of the base scheme.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A chosen one-step dévissage of a finite-type quasicoherent module `F` on
`X` over the point `s : S`. -/
structure OneStepDevissage {S : Scheme.{u}} (X : Over S) (F : X.left.Modules)
    [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] (s : S) where
  /-- The affine scheme carrying the auxiliary module. -/
  Z : Over S
  /-- The affine smooth model over the base. -/
  Y : Over S
  /-- The closed immersion of the auxiliary scheme into `X`. -/
  i : Z ⟶ X
  /-- The finite morphism from the auxiliary scheme to the smooth model. -/
  π : Z ⟶ Y
  /-- The finite-type quasicoherent module on `Z`. -/
  G : Z.left.Modules
  /-- The base scheme is affine. -/
  isAffineS : IsAffine S
  /-- The original scheme is affine. -/
  isAffineX : IsAffine X.left
  /-- The scheme carrying `G` is affine. -/
  isAffineZ : IsAffine Z.left
  /-- The smooth model is affine. -/
  isAffineY : IsAffine Y.left
  /-- The morphism `i` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i.left
  /-- The morphism `i` is of finite presentation. -/
  finitePresentation : Scheme.Hom.FinitePresentation i.left
  /-- The module `G` is quasicoherent. -/
  quasicoherent : G.IsQuasicoherent
  /-- The module `G` is of finite type. -/
  finiteType : G.IsFiniteType
  /-- The pushforward of `G` along `i` is isomorphic to `F`. -/
  moduleIso : Nonempty (F ≅ (Scheme.Modules.pushforward i.left).obj G)
  /-- The morphism `π` is finite. -/
  finite : IsFinite π.left
  /-- The structure morphism of `Y` is smooth. -/
  smooth : Smooth Y.hom
  /-- The fibres of the structure morphism of `Y` are geometrically irreducible. -/
  geometricallyIrreducible : GeometricallyIrreducible Y.hom
  /-- Every fibre of `Y` has dimension equal to the support dimension of `F`
  over `s`. -/
  fiberDimension :
    Y.hom.fiberDimension = fun _ ↦ fiberSupportDimension X.hom F s

namespace OneStepDevissage

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}

/-- Construct a one-step dévissage from an explicit affine diagram, auxiliary
module, and the defining geometric properties. -/
def ofDiagram
    (Z Y : Over S) (i : Z ⟶ X) (π : Z ⟶ Y) (G : Z.left.Modules)
    (isAffineS : IsAffine S) (isAffineX : IsAffine X.left)
    (isAffineZ : IsAffine Z.left) (isAffineY : IsAffine Y.left)
    (isClosedImmersion : IsClosedImmersion i.left)
    (finitePresentation : Scheme.Hom.FinitePresentation i.left)
    (quasicoherent : G.IsQuasicoherent) (finiteType : G.IsFiniteType)
    (moduleIso : Nonempty (F ≅ (Scheme.Modules.pushforward i.left).obj G))
    (finite : IsFinite π.left) (smooth : Smooth Y.hom)
    (geometricallyIrreducible : GeometricallyIrreducible Y.hom)
    (fiberDimension :
      Y.hom.fiberDimension = fun _ ↦ fiberSupportDimension X.hom F s) :
    OneStepDevissage X F s where
  Z := Z
  Y := Y
  i := i
  π := π
  G := G
  isAffineS := isAffineS
  isAffineX := isAffineX
  isAffineZ := isAffineZ
  isAffineY := isAffineY
  isClosedImmersion := isClosedImmersion
  finitePresentation := finitePresentation
  quasicoherent := quasicoherent
  finiteType := finiteType
  moduleIso := moduleIso
  finite := finite
  smooth := smooth
  geometricallyIrreducible := geometricallyIrreducible
  fiberDimension := fiberDimension

/-- The four schemes in a one-step dévissage are affine. -/
theorem affine_spec (D : OneStepDevissage X F s) :
    IsAffine S ∧ IsAffine X.left ∧ IsAffine D.Z.left ∧ IsAffine D.Y.left := sorry

/-- The map into `X` in a one-step dévissage is a closed immersion of finite
presentation. -/
theorem immersion_spec (D : OneStepDevissage X F s) :
    IsClosedImmersion D.i.left ∧ Scheme.Hom.FinitePresentation D.i.left := sorry

/-- The auxiliary module is finite-type quasicoherent and pushes forward to
the original module. -/
theorem module_spec (D : OneStepDevissage X F s) :
    D.G.IsQuasicoherent ∧ D.G.IsFiniteType ∧
      Nonempty (F ≅ (Scheme.Modules.pushforward D.i.left).obj D.G) := sorry

/-- The model map is finite, while the model over the base is smooth with
geometrically irreducible fibres of the prescribed dimension. -/
theorem model_spec (D : OneStepDevissage X F s) :
    IsFinite D.π.left ∧ Smooth D.Y.hom ∧ GeometricallyIrreducible D.Y.hom ∧
      D.Y.hom.fiberDimension = fun _ ↦ fiberSupportDimension X.hom F s := sorry

/-- The fibre dimension of the smooth model at any base point is the support
dimension of the original module over `s`. -/
theorem fiberDimension_apply (D : OneStepDevissage X F s) (t : S) :
    D.Y.hom.fiberDimension t = fiberSupportDimension X.hom F s := sorry

end OneStepDevissage

end AlgebraicGeometry.Scheme.Modules
