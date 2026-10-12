/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.RelativeForms
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Composition.Canonical
public import Mathlib.Algebra.Homology.CommSq

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated RingedSite.Hom
open AlgebraicGeometry.Scheme.DeRham.Cohomology

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup.DeRham

variable {S X X' : Scheme.{u}}

/-- The center immersion and the structure morphisms to the base form a commutative square. -/
theorem centerStructureSquare (f : X ⟶ S) (I : X.IdealSheafData) :
    CommSq I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) := sorry

section Maps

variable (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]

variable
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      (coefficientHom (relativeStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite (b ≫ f).toLRSHom.toShHom))]
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      (coefficientHom (centerStructureSquare f I)))
    (ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (I.subschemeι ≫ f).toLRSHom.toShHom))]
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      (coefficientHom (exceptionalInclusionStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
      (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      (coefficientHom (exceptionalStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
      (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]

/-- The canonical relative de Rham comparison from `X` to its blowup. -/
noncomputable def toBlowup :
    Scheme.DeRham.DerivedPushforward.derivedComplex f ⟶
      (modulePushforwardDerived.{u}
        (coefficientHom (relativeStructureSquare f I b))).obj
          (Scheme.DeRham.DerivedPushforward.derivedComplex (b ≫ f)) :=
  derivedPullback (relativeStructureSquare f I b)

/-- The blowup comparison is the derived de Rham pullback for its structure square. -/
theorem toBlowup_def :
    toBlowup f I b = derivedPullback (relativeStructureSquare f I b) := sorry

/-- The canonical relative de Rham comparison from `X` to the smooth center. -/
noncomputable def toCenter :
    Scheme.DeRham.DerivedPushforward.derivedComplex f ⟶
      (modulePushforwardDerived.{u}
        (coefficientHom (centerStructureSquare f I))).obj
          (Scheme.DeRham.DerivedPushforward.derivedComplex (I.subschemeι ≫ f)) :=
  derivedPullback (centerStructureSquare f I)

/-- The center comparison is the derived de Rham pullback for its structure square. -/
theorem toCenter_def :
    toCenter f I = derivedPullback (centerStructureSquare f I) := sorry

/-- The two composites of coefficient-site morphisms around the exceptional square agree. -/
theorem exceptionalCoefficientHom_eq :
    (coefficientHom (exceptionalInclusionStructureSquare f I b)).comp
        (coefficientHom (relativeStructureSquare f I b)) =
      (coefficientHom (exceptionalStructureSquare f I b)).comp
        (coefficientHom (centerStructureSquare f I)) := sorry

variable
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      ((coefficientHom (exceptionalInclusionStructureSquare f I b)).comp
        (coefficientHom (relativeStructureSquare f I b))))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
      (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]
  [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u}
      ((coefficientHom (exceptionalStructureSquare f I b)).comp
        (coefficientHom (centerStructureSquare f I))))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
      (exceptionalProjection I b ≫ I.subschemeι ≫ f).toLRSHom.toShHom))]

/-- Equal coefficient-site composites induce equal derived direct-image functors. -/
theorem exceptionalCompositeDerivedPushforward_eq :
    modulePushforwardDerived.{u}
        ((coefficientHom (exceptionalInclusionStructureSquare f I b)).comp
          (coefficientHom (relativeStructureSquare f I b))) =
      modulePushforwardDerived.{u}
        ((coefficientHom (exceptionalStructureSquare f I b)).comp
          (coefficientHom (centerStructureSquare f I))) := sorry

variable
  [((coefficientHom
    (exceptionalInclusionStructureSquare f I b)).modulePushforward.{u}).IsRightAdjoint]
  [((coefficientHom
    (relativeStructureSquare f I b)).modulePushforward.{u}).IsRightAdjoint]
  [((coefficientHom
    (exceptionalStructureSquare f I b)).modulePushforward.{u}).IsRightAdjoint]
  [((coefficientHom
    (centerStructureSquare f I)).modulePushforward.{u}).IsRightAdjoint]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      (coefficientHom (exceptionalInclusionStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite (b ≫ f).toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      (coefficientHom (relativeStructureSquare f I b)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      ((coefficientHom (exceptionalInclusionStructureSquare f I b)).comp
        (coefficientHom (relativeStructureSquare f I b))))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      (coefficientHom (exceptionalStructureSquare f I b)))
    (ModuleQis.{u}
      (RingedSpace.DeRham.coefficientSite (I.subschemeι ≫ f).toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      (coefficientHom (centerStructureSquare f I)))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u}
      ((coefficientHom (exceptionalStructureSquare f I b)).comp
        (coefficientHom (centerStructureSquare f I))))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))]
  [DerivedAdjunction.HasPair.{u}
    (coefficientHom (exceptionalInclusionStructureSquare f I b))]
  [DerivedAdjunction.HasPair.{u}
    (coefficientHom (relativeStructureSquare f I b))]
  [DerivedAdjunction.HasPair.{u}
    ((coefficientHom (exceptionalInclusionStructureSquare f I b)).comp
      (coefficientHom (relativeStructureSquare f I b)))]
  [DerivedAdjunction.HasPair.{u}
    (coefficientHom (exceptionalStructureSquare f I b))]
  [DerivedAdjunction.HasPair.{u}
    (coefficientHom (centerStructureSquare f I))]
  [DerivedAdjunction.HasPair.{u}
    ((coefficientHom (exceptionalStructureSquare f I b)).comp
      (coefficientHom (centerStructureSquare f I)))]
  [IsIso (modulePullbackDerived.compComparison
    (coefficientHom (exceptionalInclusionStructureSquare f I b))
    (coefficientHom (relativeStructureSquare f I b)))]
  [IsIso (modulePullbackDerived.compComparison
    (coefficientHom (exceptionalStructureSquare f I b))
    (coefficientHom (centerStructureSquare f I)))]

/-- The canonical identification of the two iterated derived direct images from the
exceptional divisor to `X`. -/
noncomputable def exceptionalPushforwardIso :
    (modulePushforwardDerived.{u}
      (coefficientHom (relativeStructureSquare f I b))).obj
        ((modulePushforwardDerived.{u}
          (coefficientHom (exceptionalInclusionStructureSquare f I b))).obj
            (Scheme.DeRham.DerivedPushforward.derivedComplex
              (exceptionalProjection I b ≫ I.subschemeι ≫ f))) ≅
      (modulePushforwardDerived.{u}
        (coefficientHom (centerStructureSquare f I))).obj
          ((modulePushforwardDerived.{u}
            (coefficientHom (exceptionalStructureSquare f I b))).obj
              (Scheme.DeRham.DerivedPushforward.derivedComplex
                (exceptionalProjection I b ≫ I.subschemeι ≫ f))) :=
  (modulePushforwardDerived.compIso
      (coefficientHom (exceptionalInclusionStructureSquare f I b))
      (coefficientHom (relativeStructureSquare f I b)) inferInstance).app _ ≪≫
    eqToIso (congrArg
      (fun F ↦ F.obj (Scheme.DeRham.DerivedPushforward.derivedComplex
        (exceptionalProjection I b ≫ I.subschemeι ≫ f)))
      (exceptionalCompositeDerivedPushforward_eq f I b)) ≪≫
    ((modulePushforwardDerived.compIso
      (coefficientHom (exceptionalStructureSquare f I b))
      (coefficientHom (centerStructureSquare f I)) inferInstance).app _).symm

/-- The component of `exceptionalPushforwardIso` is the composite of the two canonical
derived-pushforward composition isomorphisms and coefficient-square transport. -/
theorem exceptionalPushforwardIso_hom_app :
    (exceptionalPushforwardIso f I b).hom =
      (modulePushforwardDerived.compIso
        (coefficientHom (exceptionalInclusionStructureSquare f I b))
        (coefficientHom (relativeStructureSquare f I b)) inferInstance).hom.app _ ≫
      eqToHom (congrArg
        (fun F ↦ F.obj (Scheme.DeRham.DerivedPushforward.derivedComplex
          (exceptionalProjection I b ≫ I.subschemeι ≫ f)))
        (exceptionalCompositeDerivedPushforward_eq f I b)) ≫
      (modulePushforwardDerived.compIso
        (coefficientHom (exceptionalStructureSquare f I b))
        (coefficientHom (centerStructureSquare f I)) inferInstance).inv.app _ := sorry

/-- The canonical comparison from the blowup term to the iterated exceptional term. -/
noncomputable def blowupToExceptional :
    (modulePushforwardDerived.{u}
      (coefficientHom (relativeStructureSquare f I b))).obj
        (Scheme.DeRham.DerivedPushforward.derivedComplex (b ≫ f)) ⟶
      (modulePushforwardDerived.{u}
        (coefficientHom (centerStructureSquare f I))).obj
          ((modulePushforwardDerived.{u}
            (coefficientHom (exceptionalStructureSquare f I b))).obj
              (Scheme.DeRham.DerivedPushforward.derivedComplex
                (exceptionalProjection I b ≫ I.subschemeι ≫ f))) :=
  (modulePushforwardDerived.{u}
    (coefficientHom (relativeStructureSquare f I b))).map
      (derivedPullback (exceptionalInclusionStructureSquare f I b)) ≫
    (exceptionalPushforwardIso f I b).hom

/-- The blowup-to-exceptional map is obtained by direct image of the exceptional restriction
followed by the canonical composition comparison. -/
theorem blowupToExceptional_def :
    blowupToExceptional f I b =
      (modulePushforwardDerived.{u}
        (coefficientHom (relativeStructureSquare f I b))).map
          (derivedPullback (exceptionalInclusionStructureSquare f I b)) ≫
        (exceptionalPushforwardIso f I b).hom := sorry

/-- The canonical comparison from the center term to the iterated exceptional term. -/
noncomputable def centerToExceptional :
    (modulePushforwardDerived.{u}
      (coefficientHom (centerStructureSquare f I))).obj
        (Scheme.DeRham.DerivedPushforward.derivedComplex (I.subschemeι ≫ f)) ⟶
      (modulePushforwardDerived.{u}
        (coefficientHom (centerStructureSquare f I))).obj
          ((modulePushforwardDerived.{u}
            (coefficientHom (exceptionalStructureSquare f I b))).obj
              (Scheme.DeRham.DerivedPushforward.derivedComplex
                (exceptionalProjection I b ≫ I.subschemeι ≫ f))) :=
  (modulePushforwardDerived.{u}
    (coefficientHom (centerStructureSquare f I))).map
      (derivedPullback (exceptionalStructureSquare f I b))

/-- The center-to-exceptional map is direct image of the exceptional-projection comparison. -/
theorem centerToExceptional_def :
    centerToExceptional f I b =
      (modulePushforwardDerived.{u}
        (coefficientHom (centerStructureSquare f I))).map
          (derivedPullback (exceptionalStructureSquare f I b)) := sorry

/-- The four canonical relative de Rham comparison maps form a commutative square. -/
theorem square :
    CommSq (toBlowup f I b) (toCenter f I)
      (blowupToExceptional f I b) (centerToExceptional f I b) := sorry

/-- The first map of the signed short complex is the lift of the blowup and center maps. -/
theorem square_shortComplex_f :
    (square f I b).shortComplex'.f = biprod.lift (toBlowup f I b) (toCenter f I) := sorry

/-- The second map of the signed short complex reverses the sign of the center comparison. -/
theorem square_shortComplex_g :
    (square f I b).shortComplex'.g =
      biprod.desc (blowupToExceptional f I b) (-centerToExceptional f I b) := sorry

/-- The signed short complex of canonical blowup and center comparisons extends to a
distinguished triangle in the coefficient-derived category on `X`. -/
theorem exists_distinguishedTriangle [Smooth f] [Smooth (I.subschemeι ≫ f)] :
    ∃ δ : (square f I b).shortComplex'.X₃ ⟶
        (square f I b).shortComplex'.X₁⟦(1 : ℤ)⟧,
      Triangle.mk (square f I b).shortComplex'.f
          (square f I b).shortComplex'.g δ ∈
        distTriang (RingedSite.Hom.ModuleDerived.{u}
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)) := sorry

end Maps

end AlgebraicGeometry.IsBlowup.DeRham
