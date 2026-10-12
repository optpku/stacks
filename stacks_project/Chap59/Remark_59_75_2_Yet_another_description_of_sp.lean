/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.Derived

open AlgebraicGeometry Scheme CategoryTheory CategoryTheory.Limits Opposite

universe u

@[expose] public section

noncomputable section

variable {S : Scheme.{u}} (s t : GeometricPoint S)
variable (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
variable (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)

/- Remark 59.75.2 (Yet another description of sp) (1): the comparison of strict
henselizations is the unique over-S morphism preserving the prescribed geometric point. -/
@[stacks 0GJ4]
#check (AlgebraicGeometry.Scheme.existsUnique_strictHenselizationComparison S s t
  (etaleLocalRing S s) (etaleLocalRing S t) point (StrictHenselization.closedPoint t)
  point_over (StrictHenselization.closedPoint_over t) :
  ∃! comparison : strictHenselizationAt S t ⟶ strictHenselizationAt S s,
    comparison ≫ StrictHenselization.toScheme S s = StrictHenselization.toScheme S t ∧
      StrictHenselization.closedPoint t ≫ comparison = point)

variable (F : Sheaf S.smallEtaleTopology (Type (u + 1)))

/- Remark 59.75.2 (Yet another description of sp) (2): independently constructed
geometric specialization agrees with genuine sections pullback along the canonical
comparison, under the canonical closed-point germ identifications. -/
@[stacks 0GJ4]
#check (AlgebraicGeometry.Scheme.etaleSpecialization_eq_strictHenselianPullback
  s t point point_over F :
  (strictHenselianGlobalToStalk (Type (u + 1)) s).app F ≫
      (((StrictHenselianNeighborhood.canonical s).specializationPoint
        point point_over).sheafFiber).app F =
    (strictHenselianGlobalSectionsPullback (Type (u + 1)) s t
      (StrictHenselization.comparison s t point point_over)
      (StrictHenselization.comparison_over s t point point_over)).app F ≫
      (strictHenselianGlobalToStalk (Type (u + 1)) t).app F)

variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [IsGrothendieckAbelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}))

/- Remark 59.75.2 (Yet another description of sp) (3): exact localization identifies
specialization with genuine derived sections pullback for every unbounded K, without
boundedness, supplied comparison isomorphisms, or injective-preservation assumptions. -/
@[stacks 0GJ4]
#check (AlgebraicGeometry.Scheme.derivedEtaleSpecialization_eq_strictHenselianPullback
  s t point point_over K :
  (strictHenselianDerivedGlobalToStalk s).app K ≫
      (ExactFunctor.MapDerivedCategory.map (ObjectProperty.homMk
        ((StrictHenselianNeighborhood.canonical s).specializationPoint
          point point_over).sheafFiber : etaleStalkExact s ⟶ etaleStalkExact t)).app K =
    (ExactFunctor.MapDerivedCategory.map (ObjectProperty.homMk
      (strictHenselianGlobalSectionsPullback AddCommGrpCat.{u + 1} s t
        (StrictHenselization.comparison s t point point_over)
        (StrictHenselization.comparison_over s t point point_over)) :
      strictHenselianGlobalSectionsExact s ⟶ strictHenselianGlobalSectionsExact t)).app K ≫
      (strictHenselianDerivedGlobalToStalk t).app K)

end
