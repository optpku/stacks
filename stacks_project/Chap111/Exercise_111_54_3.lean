module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.FunctionField
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import stacks_project.Chap53.Lemma_53_12_4_LocalRamification
public import stacks_project.Chap111.Exercise_111_54_3_Hypersurface
public import stacks_project.Chap111.Exercise_111_54_3_Projection

/-!
# Exercise 111.54.3

For a field `k` and a degree-`d` form `F` whose vanishing `C = V₊(F) ⊂ P^2_k` is a
smooth curve, the adjunction sequence `O(-d) ⟶ O ⟶ i_* O_C` is short exact, the
global functions on `C` are `k`, the genus is `((d-1)*(d-2))/2`, projection from
`(0 : 0 : 1)` has degree `d`, and under the stated ramification hypotheses the
polar `∂F/∂X_2` cuts out `d*(d-1)` ramification points with canonical sheaf
`i^* O(d-3)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

variable {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
  (hF : F ∈ ProjectiveSpace.grading k 2 d)
variable [Curve (Over.mk (hom d F hF))] [Smooth (hom d F hF)]

/-- Exercise 111.54.3 (1): if `C = V₊(F) ⊂ P^2_k` is a smooth curve over `k` with closed
immersion `i`, then `0 → O_{P^2_k}(-d) → O_{P^2_k} → i_* O_C → 0` is a short exact
sequence of coherent sheaves, where the first map is multiplication by `F` and the
second map is the adjunction unit, identified with `i_* O_C` via
`pullbackStructureSheafIso`. -/
@[stacks 06A2]
theorem structureSheafSequence_shortExact :
    (sequence d F hF).ShortExact := sorry

/-- Exercise 111.54.3 (2): the canonical map `k → H^0(C, O_C)` is bijective. -/
@[stacks 06A2]
theorem globalSectionsMap_bijective :
    Function.Bijective (Scheme.Hom.globalSectionsMap (hom d F hF)) := sorry

/-- Exercise 111.54.3 (3): the genus of `C` is `((d - 1) * (d - 2)) / 2`. -/
@[stacks 06A2]
theorem genus_eq :
    Scheme.Hom.cohomologyFinrank (hom d F hF)
        (SheafOfModules.unit (scheme d F hF).ringCatSheaf) 1 =
      ((d - 1) * (d - 2)) / 2 := sorry

/-- Exercise 111.54.3 (4): if `P = (0 : 0 : 1)` is not on `C`, then the projection
`π : C → P^1_k` given by `(a_0 : a_1 : a_2) ↦ (a_0 : a_1)` has degree `d`. -/
@[stacks 06A2]
theorem projection_degree
    (hP : centerPoint k ∉ Set.range (closedImmersion d F hF).base) :
    (projection d F hF hP).inducedFunctionFieldDegree = d := sorry

/-- Exercise 111.54.3 (5): if `k` is algebraically closed of characteristic not `2` and
every ramification index of `π` is `1` or `2`, then `π` has `d * (d - 1)` ramification
points. -/
@[stacks 06A2]
theorem ramificationPoint_ncard
    [IsAlgClosed k]
    (hP : centerPoint k ∉ Set.range (closedImmersion d F hF).base)
    (h_char : (2 : k) ≠ 0)
    (h_ramif : ∀ x : closedPoints (scheme d F hF),
      (projection d F hF hP).ramificationIndexAt x.1 = 1 ∨
        (projection d F hF hP).ramificationIndexAt x.1 = 2) :
    Set.ncard {x : closedPoints (scheme d F hF) |
        (projection d F hF hP).ramificationIndexAt x.1 = 2} =
      d * (d - 1) := sorry

/-- Exercise 111.54.3 (6): a closed point of `C` is a ramification point of `π` if and
only if its image in `P^2_k` lies on the common vanishing locus of `F` and `∂F/∂X_2`. -/
@[stacks 06A2]
theorem ramificationPoint_iff
    [IsAlgClosed k]
    (hP : centerPoint k ∉ Set.range (closedImmersion d F hF).base)
    (h_char : (2 : k) ≠ 0)
    (h_ramif : ∀ x : closedPoints (scheme d F hF),
      (projection d F hF hP).ramificationIndexAt x.1 = 1 ∨
        (projection d F hF hP).ramificationIndexAt x.1 = 2)
    (x : closedPoints (scheme d F hF)) :
    (projection d F hF hP).ramificationIndexAt x.1 = 2 ↔
      (closedImmersion d F hF).base x.1 ∈
        ProjectiveSpectrum.zeroLocus (ProjectiveSpace.grading k 2)
          {F, ramificationEquation F} := sorry

/-- Exercise 111.54.3 (7): the canonical sheaf `K_C = Ω_{C/k}` is isomorphic to
`i^* O_{P^2}(d - 3)`. -/
@[stacks 06A2]
theorem canonicalSheaf_isIsomorphic :
    IsIsomorphic
      ((Scheme.Modules.pullback (closedImmersion d F hF)).obj
        (twistingSheaf k 2 ((d : ℤ) - 3)))
      Ω[(hom d F hF).toShHom] := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
