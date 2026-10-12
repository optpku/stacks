/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import stacks_project.Chap71.Definition_71_10_1_MeromorphicFunction

/-!
# Stalks of meromorphic functions on algebraic spaces

The stalk `𝒦_{X, x̄}` of the meromorphic-function sheaf at a geometric point, and the
stalk submonoid `𝒮_{x̄}` of regular étale sections, are the fibers of `𝒦_X` and `𝒮_X`
along `toSmallEtalePoint`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Small colimits of commutative rings exist in universe `u + 1`, so site-point fibers of
lifted étale ring sheaves are available. -/
instance hasColimitsOfSize_commRingCat_succ :
    HasColimitsOfSize.{u, u} CommRingCat.{u + 1} :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} CommRingCat.{u + 1}

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The stalk of the universe-lifted commutative structure sheaf at a geometric point. -/
abbrev structureSheafLiftStalk (xbar : GeometricPoint X) : CommRingCat.{u + 1} :=
  (xbar.toSmallEtalePoint.presheafFiber :
      ((smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1}) ⥤ CommRingCat.{u + 1}).obj
    (commStructureSheafLift X).obj

/-- `structureSheafLiftStalk xbar` is the `CommRingCat`-valued étale-site fiber of the
lifted structure sheaf. -/
theorem structureSheafLiftStalk_eq (xbar : GeometricPoint X) :
    structureSheafLiftStalk xbar =
      (xbar.toSmallEtalePoint.presheafFiber :
          ((smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1}) ⥤ CommRingCat.{u + 1}).obj
        (commStructureSheafLift X).obj :=
  sorry

/-- The stalk of the meromorphic-function sheaf `𝒦_X` at a geometric point. -/
abbrev meromorphicFunctionStalk (xbar : GeometricPoint X) : CommRingCat.{u + 1} :=
  (xbar.toSmallEtalePoint.presheafFiber :
      ((smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1}) ⥤ CommRingCat.{u + 1}).obj
    (meromorphicFunctionSheaf X).obj

/-- `meromorphicFunctionStalk xbar` is the `CommRingCat`-valued étale-site fiber of `𝒦_X`. -/
theorem meromorphicFunctionStalk_eq (xbar : GeometricPoint X) :
    meromorphicFunctionStalk xbar =
      (xbar.toSmallEtalePoint.presheafFiber :
          ((smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1}) ⥤ CommRingCat.{u + 1}).obj
        (meromorphicFunctionSheaf X).obj :=
  sorry

/-- The germ of a lifted structure-sheaf section along a lift of a geometric point. -/
def structureSheafLiftGerm (xbar : GeometricPoint X) (U : smallEtaleSite X)
    (l : xbar.toSmallEtalePoint.fiber.obj U) :
    (commStructureSheafLift X).obj.obj (op U) ⟶ structureSheafLiftStalk xbar :=
  xbar.toSmallEtalePoint.toPresheafFiber U l (commStructureSheafLift X).obj

/-- `structureSheafLiftGerm` is the site-point coprojection of the lifted structure sheaf. -/
theorem structureSheafLiftGerm_eq (xbar : GeometricPoint X) (U : smallEtaleSite X)
    (l : xbar.toSmallEtalePoint.fiber.obj U) :
    structureSheafLiftGerm xbar U l =
      xbar.toSmallEtalePoint.toPresheafFiber U l (commStructureSheafLift X).obj :=
  sorry

/-- The stalk submonoid `𝒮_{x̄}` of regular étale sections of `𝒪_X` at a geometric point. -/
def meromorphicDenominatorStalk (xbar : GeometricPoint X) :
    Submonoid (structureSheafLiftStalk xbar) :=
  ⨆ (U : smallEtaleSite X) (l : xbar.toSmallEtalePoint.fiber.obj U),
    Submonoid.map (structureSheafLiftGerm xbar U l).hom
      ((regularStructureSections X).obj (op U))

/-- `meromorphicDenominatorStalk xbar` is the join of germs of regular étale sections. -/
theorem meromorphicDenominatorStalk_eq (xbar : GeometricPoint X) :
    meromorphicDenominatorStalk xbar =
      ⨆ (U : smallEtaleSite X) (l : xbar.toSmallEtalePoint.fiber.obj U),
        Submonoid.map (structureSheafLiftGerm xbar U l).hom
          ((regularStructureSections X).obj (op U)) :=
  sorry

/-- Membership in `𝒮_{x̄}` is witnessed by a regular étale section germ. -/
theorem mem_meromorphicDenominatorStalk_iff (xbar : GeometricPoint X)
    (s : structureSheafLiftStalk xbar) :
    s ∈ meromorphicDenominatorStalk xbar ↔
      ∃ (U : smallEtaleSite X) (l : xbar.toSmallEtalePoint.fiber.obj U)
        (f : (commStructureSheafLift X).obj.obj (op U)),
        f ∈ (regularStructureSections X).obj (op U) ∧
          (structureSheafLiftGerm xbar U l).hom f = s :=
  sorry

/-- The stalk of `𝒪_X ⟶ 𝒦_X` makes `𝒦_{X, x̄}` an algebra over `𝒪_{X, x̄}`. -/
instance instAlgebra_meromorphicFunctionStalk (xbar : GeometricPoint X) :
    Algebra (structureSheafLiftStalk xbar) (meromorphicFunctionStalk xbar) :=
  RingHom.toAlgebra
    (xbar.toSmallEtalePoint.presheafFiber.map (toMeromorphicFunctionSheafHom X).hom).hom

/-- The algebra map `𝒪_{X, x̄} → 𝒦_{X, x̄}` is the stalk of `𝒪_X ⟶ 𝒦_X`. -/
theorem algebraMap_meromorphicFunctionStalk (xbar : GeometricPoint X) :
    algebraMap (structureSheafLiftStalk xbar) (meromorphicFunctionStalk xbar) =
      (xbar.toSmallEtalePoint.presheafFiber.map
        (toMeromorphicFunctionSheafHom X).hom).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
