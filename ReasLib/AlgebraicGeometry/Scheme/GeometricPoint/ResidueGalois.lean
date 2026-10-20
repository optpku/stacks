/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint
public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint.SeparableClosure
public import Mathlib.FieldTheory.Galois.Notation

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {S : Scheme.{u}}

/-- The separable closure of the residue field inside the source field of a geometric point. -/
@[reducible] noncomputable def separableClosure (s : GeometricPoint S) :
    IntermediateField (S.residueField s.toFieldValuedPoint.image) s.K :=
  s.toFieldValuedPoint.separableClosureOfAlgClosed s.isAlgClosed

/-- Membership in the geometric-point separable closure is separability over its residue field. -/
theorem mem_separableClosure_iff (s : GeometricPoint S) {x : s.K} :
    x ∈ s.separableClosure ↔ IsSeparable (S.residueField s.toFieldValuedPoint.image) x := sorry

/-- The absolute Galois group of the residue field of a geometric point is the group of
automorphisms of its embedded separable closure. -/
abbrev absoluteGaloisGroup (s : GeometricPoint S) :=
  Gal(s.separableClosure / S.residueField s.toFieldValuedPoint.image)

/-- The absolute Galois group is the algebra automorphism group of the separable closure. -/
theorem absoluteGaloisGroup_def (s : GeometricPoint S) :
    s.absoluteGaloisGroup =
      (s.separableClosure ≃ₐ[S.residueField s.toFieldValuedPoint.image] s.separableClosure) :=
  sorry

/-- A geometric point is algebraic when its source field is an algebraic closure of its residue field. -/
def IsAlgebraic (s : GeometricPoint S) : Prop :=
  IsAlgClosure (S.residueField s.toFieldValuedPoint.image) s.K

/-- The algebraic-point predicate unfolds to the canonical algebraic-closure property. -/
theorem isAlgebraic_def (s : GeometricPoint S) :
    s.IsAlgebraic = IsAlgClosure (S.residueField s.toFieldValuedPoint.image) s.K := sorry

/-- The algebraic-point predicate is equivalent to closedness and algebraicity over the residue field. -/
theorem isAlgebraic_iff (s : GeometricPoint S) :
    s.IsAlgebraic ↔
      IsAlgClosed s.K ∧
        Algebra.IsAlgebraic (S.residueField s.toFieldValuedPoint.image) s.K := sorry

end AlgebraicGeometry.Scheme.GeometricPoint
