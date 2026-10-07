module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.Criteria
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.19.7 -/
@[stacks 0C4D] #check
  (AlgebraicGeometry.SchemeOverField.isNode_tfae :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X]
    (h_dimension : topologicalKrullDim X.left = 1)
    (x : X.left) (h_closed : x ∈ closedPoints X.left)
    (Ash : Type u) [CommRing Ash] [Algebra (stalkRing X x) Ash]
    [IsStrictHenselizationOf (stalkRing X x) Ash],
    let A := stalkRing X x
    let κ := ResidueField A
    let V := CotangentSpace A
    let hasQuadraticRelation :=
      ∃ (e : Module.Basis (Fin 2) κ V) (a b c : κ),
        4 * a * c - b ^ 2 ≠ 0 ∧
          idealConormalAlgebraQuotient (maximalIdeal A)
              (a • SymmetricAlgebra.ι κ V (e 0) ^ 2 +
                b • (SymmetricAlgebra.ι κ V (e 0) * SymmetricAlgebra.ι κ V (e 1)) +
                c • SymmetricAlgebra.ι κ V (e 1) ^ 2) = 0
    let nodalLocalCondition :=
      Algebra.IsSeparableOver k κ ∧ _root_.IsReduced A ∧
        Module.finrank κ V = 2 ∧ hasQuadraticRelation
    let geometricCondition :=
      ∀ xbar : (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).left,
        FieldExtension.Over.toSource k (AlgebraicClosure k) X xbar = x →
          isOrdinaryDoublePoint
            (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) xbar
    let firstFittingGeneratesMaximalIdeal :=
      RingedSpace.idealSheafStalkIdeal
          (Scheme.fittingIdealSheaf (Ω[X.hom.toShHom]) 1).toSubobject x =
        maximalIdeal A
    let reducedFittingCondition :=
      Algebra.IsSeparableOver k κ ∧ _root_.IsReduced A ∧ firstFittingGeneratesMaximalIdeal
    let depthFittingCondition :=
      Algebra.IsSeparableOver k κ ∧ moduleDepth A A = 1 ∧ firstFittingGeneratesMaximalIdeal
    let normalizationCondition :=
      Algebra.IsSeparableOver k κ ∧ _root_.IsReduced A ∧ deltaInvariantAt X x = 1 ∧
        X.left.geometricBranchNumberAt x Ash = 2
    List.TFAE
      [isNode X x, nodalLocalCondition, geometricCondition, reducedFittingCondition,
        depthFittingCondition, normalizationCondition])

end AlgebraicGeometry.SchemeOverField
