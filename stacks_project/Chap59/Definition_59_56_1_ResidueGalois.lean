module

public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.Galois.Notation

open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.FieldValuedPoint

variable {X : Scheme.{u}}

/-- The algebra structure on a source field induced by the residue-field map at its image. -/
noncomputable instance residueFieldAlgebra (p : FieldValuedPoint X) :
    Algebra (X.residueField p.image) p.K :=
  p.residueFieldHom.hom.toAlgebra

/-- The algebra map of `residueFieldAlgebra` is the canonical residue-field homomorphism. -/
theorem algebraMap_residueFieldAlgebra (p : FieldValuedPoint X) :
    algebraMap (X.residueField p.image) p.K = p.residueFieldHom.hom := sorry

end AlgebraicGeometry.Scheme.FieldValuedPoint

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {S : Scheme.{u}}

/-- The separable closure of the residue field inside the source field of a geometric point. -/
noncomputable def separableClosure (s : GeometricPoint S) :
    IntermediateField (S.residueField s.toFieldValuedPoint.image) s.K :=
  _root_.separableClosure (S.residueField s.toFieldValuedPoint.image) s.K

/-- Membership in the geometric-point separable closure is separability over its residue field. -/
theorem mem_separableClosure_iff (s : GeometricPoint S) {x : s.K} :
    x ∈ s.separableClosure ↔ IsSeparable (S.residueField s.toFieldValuedPoint.image) x := sorry

/-- The geometric-point separable closure is a separable closure of the residue field. -/
instance separableClosureIsSepClosure (s : GeometricPoint S) :
    IsSepClosure (S.residueField s.toFieldValuedPoint.image) s.separableClosure := sorry

/-- The absolute Galois group of the residue field of a geometric point, as Gal of
its point-specific separable closure. -/
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
