module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.Algebra.Module.IdealPower.Serre
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic
public import stacks_project.Chap81.Lemma_81_10_4_IdealStalk

/-!
# Lemma 81.10.4

The étale derived stalk of a quasi-coherent complex supported on the closed image of
a finite-presentation closed immersion has ideal-power-torsion cohomology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 81.10.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`i : Z ⟶ X` be a closed immersion of finite presentation. Let `Q` in `DerivedQCoh X`
be supported on `|Z| = pointsImage i`. Let `xbar` be a geometric point of `X` and let
`Hom.idealSheafStalkIdeal i xbar ⊂ etaleLocalRing X xbar` be the stalk of the ideal
sheaf of `Z`. Then the cohomology modules `H^n(Q_xbar)` are
`Hom.idealSheafStalkIdeal i xbar`-power torsion in the sense of
`Module.IsIdealPowerTorsion` (Definition 15.89.1). -/
@[stacks 0AET]
theorem stalkDerived_cohomology_isIdealPowerTorsion {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] [FinitePresentation i]
    (Q : DerivedQCoh X) (hQ : IsSupportedOn Q.obj (pointsImage i))
    (xbar : GeometricPoint X) (n : ℤ) :
    Module.IsIdealPowerTorsion (Hom.idealSheafStalkIdeal i xbar)
      ((DerivedCategory.homologyFunctor (ModuleCat (etaleLocalRing X xbar)) n).obj
        (stalkDerived xbar Q.obj)) :=
  sorry

/-- The derived étale stalk of a quasi-coherent complex supported on `|Z|` has
`Hom.idealSheafStalkIdeal i xbar`-power-torsion cohomology in every degree. -/
theorem stalkDerived_mem_idealPowerTorsion {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] [FinitePresentation i] (Q : DerivedQCoh X)
    (hQ : IsSupportedOn Q.obj (pointsImage i)) (xbar : GeometricPoint X) :
    DerivedCategory.cohomologyIn
      (ModuleCat.isIdealPowerTorsion (Hom.idealSheafStalkIdeal i xbar))
      (stalkDerived xbar Q.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
