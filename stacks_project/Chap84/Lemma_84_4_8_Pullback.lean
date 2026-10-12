/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap84.Theorem_84_4_6_Comparison

/-!
# Geometric fibres of morphisms of algebraic spaces

The chosen fibre `ȳ ×_Y X` of a morphism of algebraic spaces at a geometric
point of the target, together with its projections and the inverse image of
abelian or derived coefficients along the map to `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open GeometricPoint

/-- The geometric fibre `X_ȳ = ȳ ×_Y X` of `f` at a geometric point `ȳ` of `Y`. -/
noncomputable abbrev geometricFiber {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ybar : GeometricPoint Y) : AlgebraicSpace S :=
  pullback ybar.hom f

/-- `geometricFiber` is the chosen fibre product `ȳ ×_Y X`. -/
theorem geometricFiber_def {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    geometricFiber f ybar = pullback ybar.hom f :=
  rfl

/-- The structure morphism `f' : ȳ ×_Y X ⟶ Spec κ(ȳ)` of the geometric fibre. -/
noncomputable abbrev geometricFiberToPoint {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    geometricFiber f ybar ⟶ ofOver ybar.overObj :=
  pullback.fst ybar.hom f

/-- `geometricFiberToPoint` is the first projection of `ȳ ×_Y X`. -/
theorem geometricFiberToPoint_def {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    geometricFiberToPoint f ybar = pullback.fst ybar.hom f :=
  rfl

/-- The base-change morphism `g' : ȳ ×_Y X ⟶ X` of the geometric fibre. -/
noncomputable abbrev geometricFiberToX {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    geometricFiber f ybar ⟶ X :=
  pullback.snd ybar.hom f

/-- `geometricFiberToX` is the second projection of `ȳ ×_Y X`. -/
theorem geometricFiberToX_def {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    geometricFiberToX f ybar = pullback.snd ybar.hom f :=
  rfl

/-- The cartesian square presenting the geometric fibre, in the `84.4.6` orientation
`g'`, `f'` over `f`, `ȳ`. -/
theorem geometricFiber_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    IsPullback (geometricFiberToX f ybar) (geometricFiberToPoint f ybar) f ybar.hom :=
  (IsPullback.of_hasPullback ybar.hom f).flip

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `smallEtaleDerivedInverseImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
variable (f : X ⟶ Y) (ybar : GeometricPoint Y)

/-- Inverse image of an abelian small-étale sheaf along the geometric-fibre inclusion
`ȳ ×_Y X ⟶ X`. This is the source sheaf `F_ȳ`, not a stalk of `F` on `X`. -/
noncomputable abbrev geometricFiberAbelianSheaf
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1} :=
  (sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).obj F

/-- `geometricFiberAbelianSheaf` is inverse image along `geometricFiberToX`. -/
theorem geometricFiberAbelianSheaf_eq
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    geometricFiberAbelianSheaf f ybar F =
      (sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).obj F :=
  rfl

variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]

/-- Derived inverse image of a bounded-below complex along the geometric-fibre inclusion.
This is the source object `E_ȳ` on `D⁺((ȳ ×_Y X)_étale)`. -/
noncomputable abbrev geometricFiberDerived
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    DerivedCategory.Plus
      (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}) :=
  (smallEtaleDerivedInverseImage (geometricFiberToX f ybar)).obj E

/-- `geometricFiberDerived` is `smallEtaleDerivedInverseImage` along `geometricFiberToX`. -/
theorem geometricFiberDerived_eq
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    geometricFiberDerived f ybar E =
      (smallEtaleDerivedInverseImage (geometricFiberToX f ybar)).obj E :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
