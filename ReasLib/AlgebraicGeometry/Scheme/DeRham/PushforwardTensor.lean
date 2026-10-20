module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CoefficientTensor
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Pullback
public import ReasLib.CategoryTheory.Functor.Derived.TensorComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open RingedSite.Hom
-- Local instance justification (defeq pin): the tensor counits use the canonical derived category of the coefficient sheaf presentation.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.DeRham.CanonicalTensor

variable {X Y S T : Scheme.{u}} {f : X ⟶ Y} {p : X ⟶ S} {q : Y ⟶ T} {h : S ⟶ T}
variable (sq : CommSq f p q h)

/-- The coefficient-site direct image is a right adjoint to inverse image of modules. -/
theorem coefficientPushforward_rightAdjoint :
    ((Cohomology.coefficientHom sq).modulePushforward.{u}).IsRightAdjoint := by
  infer_instance

-- Local instance justification (defeq pin): all derived functors below use this one coefficient morphism and its canonical underived adjunction.
attribute [local instance] coefficientPushforward_rightAdjoint

/-- Module inverse image on the coefficient sites admits its unbounded total left derived functor. -/
theorem coefficientPullback_hasLeftDerived :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{u} (Cohomology.coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) := sorry

/-- Module direct image on the coefficient sites admits its unbounded total right derived functor. -/
theorem coefficientPushforward_hasRightDerived :
    Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) :=
  modulePushforwardToDerived.hasRightDerived (Cohomology.coefficientHom sq)

-- Local instance justification (defeq pin): use the specified total-derived owners and their canonical units and counits throughout the tensor comparison.
attribute [local instance] coefficientPullback_hasLeftDerived coefficientPushforward_hasRightDerived

/-- The coefficient pullback and direct image have the absolute derived composite properties
which construct their derived adjunction. -/
theorem coefficientDerivedAdjunction_hasPair :
    DerivedAdjunction.HasPair.{u} (Cohomology.coefficientHom sq) := sorry

-- Local instance justification (defeq pin): the adjunction mate uses the fixed total-derived pair, not a separately supplied adjunction.
attribute [local instance] coefficientDerivedAdjunction_hasPair hasCoefficientDerivedTensor

/-- The actual total-derived coefficient pullback. -/
abbrev pullback := modulePullbackDerived.{u} (Cohomology.coefficientHom sq)

/-- The actual total-derived coefficient direct image. -/
abbrev pushforward := modulePushforwardDerived.{u} (Cohomology.coefficientHom sq)

/-- The canonical adjunction between the two specified total-derived functors. -/
def adjunction : pullback sq ⊣ pushforward sq :=
  moduleDerivedAdjunction.{u} (Cohomology.coefficientHom sq)

/-- Derived coefficient direct image uses the canonical total-right-derived shift comparison. -/
theorem coefficientPushforward_hasPointwiseRightDerived :
    (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq)).HasPointwiseRightDerivedFunctor
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) := sorry

-- Local instance justification (defeq pin): the total-right-derived shift is obtained from the fixed pointwise right-derived functor, whose values are given by K-injective resolutions.
attribute [local instance] coefficientPushforward_hasPointwiseRightDerived

/-- The direct-image shift data is the standard total-derived construction. -/
abbrev pushforwardCommShift : (pushforward sq).CommShift ℤ :=
  Functor.totalRightDerived_commShift
    (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
    (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))

/-- The monoidal structure of underived coefficient pullback comes from pullback of
modules over the actual commutative structure sheaves. -/
abbrev underivedPullbackMonoidal : (Cohomology.coefficientHom sq).modulePullback.{u}.Monoidal := by
  infer_instance

-- Local instance justification (defeq pin): descend the tensor comparison of this concrete module pullback to homotopy objects, using its canonical invertibility theorem.
attribute [local instance] underivedPullbackMonoidal
  modulePullbackHomotopy.TensorComparison.isInvertible

/-- The tensorator on ordinary homotopy pullback, before deriving tensor. -/
def homotopyTensorator :
    (modulePullbackHomotopy.{u} (Cohomology.coefficientHom sq)).prod
        (modulePullbackHomotopy.{u} (Cohomology.coefficientHom sq)) ⋙
      MonoidalCategory.tensor
        (ModuleHomotopy.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) ≅
    MonoidalCategory.tensor
        (ModuleHomotopy.{u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) ⋙
      modulePullbackHomotopy.{u} (Cohomology.coefficientHom sq) :=
  Functor.Monoidal.μNatIso (modulePullbackHomotopy.{u} (Cohomology.coefficientHom sq))

/-- The specified counit of total derived coefficient pullback. -/
abbrev pullbackCounit :
    moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom) ⋙
      pullback sq ⟶
    modulePullbackHomotopy.{u} (Cohomology.coefficientHom sq) ⋙
      moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) :=
  (modulePullbackToDerived.{u} (Cohomology.coefficientHom sq)).totalLeftDerivedCounit
    (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))

/-- The derived tensor counit in the tensor-then-localize presentation. -/
abbrev tensorCounit {X S : Scheme.{u}} (p : X ⟶ S) :
    (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).prod
        (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) ⋙
      tensor p ⟶
    MonoidalCategory.tensor
        (ModuleHomotopy.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) ⋙
      moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) :=
  DerivedCategory.DerivedTensor.Bifunctor.counit ≫
    DerivedCategory.DerivedTensor.Bifunctor.sourceFunctorIso.inv

open Functor.LeftDerived

/-- The specified iterated counit for derived pullback in both variables followed by
derived tensor has the left-derived universal property, as computed on K-flat resolutions. -/
theorem targetIsLeftDerived :
    ((pullback sq).prod (pullback sq) ⋙ tensor p).IsLeftDerivedFunctor
      (TensorComparison.targetCounit
        (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
        (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
        (modulePullbackHomotopy.{u} (Cohomology.coefficientHom sq)) (pullback sq)
        (MonoidalCategory.tensor
          (ModuleHomotopy.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)))
        (tensor p) (pullbackCounit sq) (tensorCounit p))
      (DerivedCategory.DerivedTensor.Bifunctor.qis
        (C := RingedSpace.DeRham.Modules q.toLRSHom.toShHom)) := sorry

/-- The canonical derived pullback tensor comparison obtained by deriving the
underived tensorator with the two specified derivation counits. -/
def pullbackTensorComparison :
    tensor q ⋙ pullback sq ⟶ (pullback sq).prod (pullback sq) ⋙ tensor p :=
  TensorComparison.comparisonOf
    (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
    (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
    (modulePullbackHomotopy.{u} (Cohomology.coefficientHom sq)) (pullback sq)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)))
    (MonoidalCategory.tensor
      (ModuleHomotopy.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)))
    (tensor q) (tensor p)
    (DerivedCategory.DerivedTensor.Bifunctor.qis
      (C := RingedSpace.DeRham.Modules q.toLRSHom.toShHom))
    (pullbackCounit sq) (tensorCounit q) (tensorCounit p)
    (homotopyTensorator sq) (targetIsLeftDerived sq)

/-- The direct-image tensor comparison is the adjunction mate of the derived
pullback comparison, followed by the tensor of the two adjunction counits. -/
def pushforwardTensorator
    (K L : ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) :
    (tensor q).obj ((pushforward sq).obj K, (pushforward sq).obj L) ⟶
      (pushforward sq).obj ((tensor p).obj (K, L)) :=
  (adjunction sq).homEquiv _ _
    ((pullbackTensorComparison sq).app ((pushforward sq).obj K, (pushforward sq).obj L) ≫
      (tensor p).map (Prod.mkHom ((adjunction sq).counit.app K) ((adjunction sq).counit.app L)))

/-- Relative derived cup multiplication is the direct-image tensorator followed
by direct image of the counit-and-wedge multiplication. -/
def cupProduct :
    (tensor q).obj
      ((pushforward sq).obj (DerivedPushforward.derivedComplex p),
       (pushforward sq).obj (DerivedPushforward.derivedComplex p)) ⟶
      (pushforward sq).obj (DerivedPushforward.derivedComplex p) :=
  pushforwardTensorator sq (DerivedPushforward.derivedComplex p) (DerivedPushforward.derivedComplex p) ≫
    (pushforward sq).map (multiplication p)

end AlgebraicGeometry.Scheme.DeRham.CanonicalTensor
