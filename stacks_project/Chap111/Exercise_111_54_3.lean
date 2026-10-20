module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Cohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Projection
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Adjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve
open scoped AlgebraicGeometry

universe u

/- Exercise 111.54.3 (1) -/
@[stacks 06A2]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.structureSheafSequence_shortExact :
  ∀ {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)],
    (Hypersurface.sequence 2 d F hF).ShortExact)

/- Exercise 111.54.3 (2) -/
@[stacks 06A2]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.globalSectionsMap_bijective :
  ∀ {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)],
    Function.Bijective (Scheme.Hom.globalSectionsMap (Hypersurface.hom 2 d F hF)))

/- Exercise 111.54.3 (3) -/
@[stacks 06A2]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.genus_eq :
  ∀ {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)],
    Scheme.Hom.cohomologyFinrank (Hypersurface.hom 2 d F hF)
        (SheafOfModules.unit (Hypersurface.scheme 2 d F hF).ringCatSheaf) 1 =
      ((d - 1) * (d - 2)) / 2)

/- Exercise 111.54.3 (4) -/
@[stacks 06A2]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.projection_degree :
  ∀ {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)]
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base),
    (projection d F hF hP).inducedFunctionFieldDegree = d)

/- Exercise 111.54.3 (5) -/
@[stacks 06A2]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.ramificationPoint_ncard :
  ∀ {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)]
    [IsAlgClosed k]
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base)
    (_h_char : (2 : k) ≠ 0)
    (_h_ramif : ∀ x : closedPoints (Hypersurface.scheme 2 d F hF),
      (projection d F hF hP).ramificationIndexAt x.1 = 1 ∨
        (projection d F hF hP).ramificationIndexAt x.1 = 2),
    Set.ncard {x : closedPoints (Hypersurface.scheme 2 d F hF) |
        (projection d F hF hP).ramificationIndexAt x.1 = 2} =
      d * (d - 1))

/- Exercise 111.54.3 (6) -/
@[stacks 06A2]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.ramificationPoint_iff :
  ∀ {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)]
    [IsAlgClosed k]
    (hP : centerPoint k ∉ Set.range (Hypersurface.closedImmersion 2 d F hF).base)
    (_h_char : (2 : k) ≠ 0)
    (_h_ramif : ∀ x : closedPoints (Hypersurface.scheme 2 d F hF),
      (projection d F hF hP).ramificationIndexAt x.1 = 1 ∨
        (projection d F hF hP).ramificationIndexAt x.1 = 2)
    (x : closedPoints (Hypersurface.scheme 2 d F hF)),
    (projection d F hF hP).ramificationIndexAt x.1 = 2 ↔
      (Hypersurface.closedImmersion 2 d F hF).base x.1 ∈
        ProjectiveSpectrum.zeroLocus (ProjectiveSpace.grading k 2)
          {F, ramificationEquation F})

/- Exercise 111.54.3 (7) -/
@[stacks 06A2]
#check (AlgebraicGeometry.ProjectiveSpace.PlaneCurve.canonicalSheaf_isIsomorphic :
  ∀ {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
    (hF : F ∈ ProjectiveSpace.grading k 2 d)
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)],
    IsIsomorphic
      ((Scheme.Modules.pullback (Hypersurface.closedImmersion 2 d F hF)).obj
        (twistingSheaf k 2 ((d : ℤ) - 3)))
      Ω[(Hypersurface.hom 2 d F hF).toShHom])

