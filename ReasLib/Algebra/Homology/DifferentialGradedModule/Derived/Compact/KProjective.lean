/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Bounded
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Limits
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Compact.FiniteCell
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Graded.FiniteProjective
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.KProjective
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KProjective
public import ReasLib.CategoryTheory.Preadditive.CompactObject

/-!
# Retracts of Finite K-Projective Derived Objects

This leaf owns the finite K-projective object property and its compactness comparison.  For any
cochain DGA, compact derived objects form the retract closure of its essential image, by the
finite-cell criterion (09R3).

The bounded-only representative converse in 09RB is false: the DGA in 09R5 is already bounded
in degrees [-1, 0].  Over a field of characteristic two it is
`k[x,y]/(y^2)`, with `|x| = 0`, `|y| = -1`, and `d(y) = x^2 + x`.
Its compact summand corresponding to `(k,0)` over `k[x]/(x^2+x) = k × k` has no finite graded
projective representative: such modules are graded free, and base change would force equal
Euler characteristics in the two factors.  Retracts in the derived category must therefore be
retained; stability under actual DG-module retracts does not remove them.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- Finite K-projective DG-modules are finite projective after forgetting the differential and
K-projective in the intrinsic DG homotopy category. -/
@[stacks 09RB "finite graded K-projective differential graded modules"]
def finiteKProjective : ObjectProperty (DifferentialGradedModule.{u, v} A) :=
  fun P ↦ IsFiniteGradedProjective A P ∧ IsKProjective A P

/-- The two defining properties of a finite K-projective DG-module. -/
@[stacks 09RB "finite K-projective defining-property criterion"]
theorem finiteKProjective_iff (P : DifferentialGradedModule.{u, v} A) :
    finiteKProjective A P ↔ IsFiniteGradedProjective A P ∧ IsKProjective A P := sorry

/-- Finite K-projectivity is finite graded projectivity together with bijectivity of localization
on every outgoing Hom set.  This is the representation-facing criterion used to construct and
recognize compact derived objects. -/
@[stacks 09RB]
theorem finiteKProjective_iff_q_map_bijective
    (P : DifferentialGradedModule.{u, v} A) :
    finiteKProjective A P ↔
      IsFiniteGradedProjective A P ∧
        ∀ M : DifferentialGradedModule.{u, v} A,
          Function.Bijective
            ((Derived.Q A).map :
              ((toK A).obj P ⟶ (toK A).obj M) →
                ((Derived.fromModules A).obj P ⟶ (Derived.fromModules A).obj M)) := sorry

namespace FiniteKProjective

/-- Finite K-projective DG-modules are stable under retracts. -/
@[stacks 09RB "retract stability of finite K-projective modules"]
instance isStableUnderRetracts :
    (finiteKProjective A).IsStableUnderRetracts := sorry

end FiniteKProjective

/-- A finite-cell filtration has finite graded-projective underlying module: its finite free
graded successive quotients split after forgetting the differential. -/
@[stacks 09R3 "finite-cell modules are finite graded projective"]
theorem isFiniteGradedProjective_of_hasFiniteCellFiltration
    {P : DifferentialGradedModule.{u, v} A}
    (hP : PropertyP.HasFiniteCellFiltration A P) : IsFiniteGradedProjective A P := sorry

/-- Finite-cell modules are finite K-projective; property P supplies K-projectivity. -/
@[stacks 09R3 "finite-cell modules are finite K-projective"]
theorem finiteKProjective_of_hasFiniteCellFiltration
    {P : DifferentialGradedModule.{u, v} A}
    (hP : PropertyP.HasFiniteCellFiltration A P) : finiteKProjective A P := by
  refine ⟨isFiniteGradedProjective_of_hasFiniteCellFiltration A hP, ?_⟩
  obtain ⟨F⟩ := hP
  exact HasPropertyP.kProjective (F.hasPropertyP A)

namespace Derived.FiniteKProjective

/-- Remark 22.36.2 (09R1): a finite graded K-projective DG-module has compact image in the
derived category. -/
@[stacks 09R1]
theorem isCompactObject {P : DifferentialGradedModule.{u, v} A}
    (hP : finiteKProjective A P) : IsCompactObject ((Derived.fromModules A).obj P) := sorry

/-- For any DGA, compact objects are exactly the retract closure of the essential image of
finite graded K-projective modules.  This follows from 09R3, and replaces the false bounded-only
representative converse of 09RB. -/
@[stacks 09R3 "compactness as the retract closure of finite K-projective images"]
theorem isCompactObject_iff (E : Derived.Category.{u, v} A) :
    IsCompactObject E ↔
      ((finiteKProjective A).map (Derived.fromModules A)).retractClosure E := by
  constructor
  · intro hE
    apply ObjectProperty.monotone_retractClosure
      (ObjectProperty.map_monotone
        (fun _ hP ↦ finiteKProjective_of_hasFiniteCellFiltration A hP)
        (Derived.fromModules A))
    exact Derived.FiniteCell.mem_retractClosure_of_isCompactObject A hE
  · rintro ⟨Y, ⟨P, hP, ⟨e⟩⟩, ⟨r⟩⟩
    apply Derived.FiniteCell.isCompactObject_of_mem_retractClosure A
    exact ((Derived.finiteCell A).retractClosure).prop_of_retract
      (r.trans e.symm.retract)
      (Derived.FiniteCell.mem_retractClosure_of_isCompactObject A (isCompactObject A hP))

/-- Explicit retract formulation: the identity of a compact object factors through the derived
image of a finite graded K-projective module.  No boundedness assumption is needed, and no
isomorphism with that image is asserted. -/
@[stacks 09R3 "compactness by explicit finite K-projective retract maps"]
theorem isCompactObject_iff_exists (E : Derived.Category.{u, v} A) :
    IsCompactObject E ↔
      ∃ (P : DifferentialGradedModule.{u, v} A),
        IsFiniteGradedProjective A P ∧ IsKProjective A P ∧
          ∃ (i : E ⟶ (Derived.fromModules A).obj P)
            (r : (Derived.fromModules A).obj P ⟶ E), i ≫ r = 𝟙 E := by
  rw [isCompactObject_iff A E]
  constructor
  · rintro ⟨Y, ⟨P, hP, ⟨e⟩⟩, ⟨s⟩⟩
    let t := s.trans e.symm.retract
    exact ⟨P, hP.1, hP.2, t.i, t.r, t.retract⟩
  · rintro ⟨P, hfin, hK, i, r, hir⟩
    exact ⟨(Derived.fromModules A).obj P,
      ⟨P, ⟨hfin, hK⟩, ⟨Iso.refl _⟩⟩, ⟨⟨i, r, hir⟩⟩⟩

end Derived.FiniteKProjective

#synth (finiteKProjective A).IsStableUnderRetracts
#synth (finiteKProjective A).IsClosedUnderIsomorphisms

end DifferentialGradedModule
