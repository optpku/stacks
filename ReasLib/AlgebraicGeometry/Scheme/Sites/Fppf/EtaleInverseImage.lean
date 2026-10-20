module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleCohomology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fppf and étale inverse images

The topology-comparison functors and small-to-big étale inverse image define inverse
images of abelian sheaves and bounded-below derived objects on the big fppf site.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FppfEtale

/-- Direct image `ε_{X,*}` on abelian sheaves from the big fppf slice to the big étale slice. -/
abbrev epsilonPushforward (X : Scheme.{u}) :
    Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  comparisonTopologyPushforwardAb (τ := fppfTopology) (τ' := etaleTopology)
    (Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage) X

/-- Inverse image `ε_X⁻¹` on abelian sheaves from the big étale slice to the big fppf slice. -/
abbrev epsilonPullback (X : Scheme.{u}) :
    Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1} :=
  comparisonTopologyPullbackAb (τ := fppfTopology) (τ' := etaleTopology)
    (Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage) X

/-- Inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on abelian sheaves from the small étale site of `X`
to the big fppf slice. -/
abbrev aInverseAb (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1} :=
  piInverseImage X ⋙ epsilonPullback X

/-- Inverse image `a_X⁻¹` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
theorem aInverseAb_eq (X : Scheme.{u}) :
    aInverseAb X = piInverseImage X ⋙ epsilonPullback X := rfl

/-- The canonical comparison map `π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)`. -/
def aInverse_unit (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (piInverseImage X).obj F ⟶
      (epsilonPushforward X).obj ((aInverseAb X).obj F) :=
  (comparisonTopologyAdjunction AddCommGrpCat.{u + 1}
      (Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage) X).unit.app
    ((piInverseImage X).obj F)

/-- `aInverse_unit` is the topology-comparison adjunction unit at `π_X⁻¹ F`. -/
theorem aInverse_unit_eq (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    aInverse_unit X F =
      (comparisonTopologyAdjunction AddCommGrpCat.{u + 1}
      (Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage) X).unit.app
        ((piInverseImage X).obj F) := rfl

/-- Inverse image `π_X⁻¹` preserves finite limits. -/
instance piInverseImage_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (piInverseImage X) := sorry

/-- Direct image of abelian small-étale sheaves along a morphism of schemes. -/
abbrev smallPushforwardAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- `smallPushforwardAb` is sheaf pushforward along `smallEtalePullback`. -/
theorem smallPushforwardAb_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallPushforwardAb f =
      (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology := rfl

/-- Direct image of abelian sheaves along a morphism of schemes on the big fppf slices. -/
abbrev fppfPushforwardAb {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (fppfTopology.over Y) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (fppfTopology.over X) (fppfTopology.over Y)

/-- `fppfPushforwardAb` is the cocontinuous sheaf pushforward along `Over.map`. -/
theorem fppfPushforwardAb_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fppfPushforwardAb f =
      (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (fppfTopology.over X) (fppfTopology.over Y) := rfl

/-- Exact inverse image `π_X⁻¹` on abelian small-étale sheaves. -/
abbrev piExact (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  ⟨piInverseImage X, piInverseImage_preservesFiniteLimits X,
    ⟨fun _ _ _ => (piAdjunction X).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩⟩

/-- Bounded-below derived inverse image `π_X⁻¹` on `D⁺`. -/
abbrev piInverseImagePlus (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (piExact X)

/-- Bounded-below derived inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on `D⁺`. -/
abbrev aInverseAbPlus (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1}) :=
  piInverseImagePlus X ⋙ Derived.Plus.pullback
    (Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage) X

/-- Derived inverse image `a_X⁻¹` is the composite of derived `π_X⁻¹` with topology-comparison
inverse image. -/
theorem aInverseAbPlus_eq (X : Scheme.{u}) :
    aInverseAbPlus X = piInverseImagePlus X ⋙ Derived.Plus.pullback
    (Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage) X :=
  rfl

end AlgebraicGeometry.Scheme.FppfEtale

end
