module

import Lean

public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableClosure
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {S : Scheme.{u}}

/-- The algebra structure on the source field induced by the residue-field map at the image.
This realizes the inclusion `κ(s) ⟶ K` for a geometric point with source field `K`. -/
@[reducible]
noncomputable def residueFieldAlgebra (s : GeometricPoint S) :
    Algebra (S.residueField s.toFieldValuedPoint.image) s.toFieldValuedPoint.K :=
  s.toFieldValuedPoint.residueFieldHom.hom.toAlgebra

/-- The induced algebra map agrees with the scheme-theoretic residue-field map. -/
theorem algebraMap_residueFieldAlgebra (s : GeometricPoint S) :
    @algebraMap (S.residueField s.toFieldValuedPoint.image)
      s.toFieldValuedPoint.K
      (inferInstance : CommSemiring (S.residueField s.toFieldValuedPoint.image))
      (inferInstance : Semiring s.toFieldValuedPoint.K)
      (residueFieldAlgebra s) =
      s.toFieldValuedPoint.residueFieldHom.hom := sorry

/- Definition 59.56.1 (1): the separable closure and absolute Galois group
of a residue field use the canonical field-theory constructions. -/
@[stacks 03QX] #check Field.absoluteGaloisGroup
@[stacks 03QX] #check @separableClosure

/-- Definition 59.56.1 (2): a geometric point is algebraic when its source field
is an algebraic closure of the residue field at its image. -/
@[stacks 03QX]
noncomputable def IsAlgebraic (s : GeometricPoint S) : Prop :=
  IsAlgClosed s.toFieldValuedPoint.K ∧
    @Algebra.IsAlgebraic (S.residueField s.toFieldValuedPoint.image)
      s.toFieldValuedPoint.K
      (inferInstance : CommRing (S.residueField s.toFieldValuedPoint.image))
      (inferInstance : Ring s.toFieldValuedPoint.K)
      (residueFieldAlgebra s)

/-- Algebraicity of a geometric point is equivalent to algebraicity of its source
field over the residue field, since the source is already algebraically closed. -/
theorem isAlgebraic_iff (s : GeometricPoint S) :
    IsAlgebraic s ↔
      IsAlgClosed s.toFieldValuedPoint.K ∧
        @Algebra.IsAlgebraic (S.residueField s.toFieldValuedPoint.image)
          s.toFieldValuedPoint.K
          (inferInstance : CommRing (S.residueField s.toFieldValuedPoint.image))
          (inferInstance : Ring s.toFieldValuedPoint.K)
          (residueFieldAlgebra s) := sorry

end AlgebraicGeometry.Scheme.GeometricPoint


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
