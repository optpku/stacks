/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FieldValuedPoint

variable {X : Scheme.{u}}

/-- The algebra structure on a source field induced by the residue-field map at its image. -/
noncomputable instance residueFieldAlgebra (p : FieldValuedPoint X) :
    Algebra (X.residueField p.image) p.K :=
  p.residueFieldHom.hom.toAlgebra

/-- The algebra map of `residueFieldAlgebra` is the canonical residue-field homomorphism. -/
theorem algebraMap_residueFieldAlgebra (p : FieldValuedPoint X) :
    algebraMap (X.residueField p.image) p.K = p.residueFieldHom.hom := sorry

/-- The separable closure of the image residue field inside an algebraically closed source field. -/
noncomputable def separableClosureOfAlgClosed (p : FieldValuedPoint X)
    (isAlgClosed : IsAlgClosed p.K) : IntermediateField (X.residueField p.image) p.K :=
  _root_.separableClosure (X.residueField p.image) p.K

/-- The relative separable closure in an algebraically closed source field is an absolute
separable closure of the image residue field. -/
instance separableClosureOfAlgClosedIsSepClosure (p : FieldValuedPoint X)
    (isAlgClosed : IsAlgClosed p.K) :
    IsSepClosure (X.residueField p.image) (p.separableClosureOfAlgClosed isAlgClosed) := sorry

/-- The relative separable closure in an algebraically closed source field is separably closed. -/
instance separableClosureOfAlgClosedIsSepClosed (p : FieldValuedPoint X)
    (isAlgClosed : IsAlgClosed p.K) :
    IsSepClosed (p.separableClosureOfAlgClosed isAlgClosed) :=
  IsSepClosure.sep_closed (X.residueField p.image)

end AlgebraicGeometry.Scheme.FieldValuedPoint
