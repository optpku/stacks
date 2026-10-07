module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber.Curve.Separable
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

/- Lemma 37.65.4 (Variant with separable extensions over curves): for a flat finite-type
morphism `f : X ⟶ S`, where `S` is Nagata, integral, regular, and one-dimensional and the
residue fields at generic points of the generic fibre are separable over `S.functionField`,
the finite function-field extension producing a normalized base change smooth in codimension
zero can be chosen separable. -/
@[stacks 0BRS] #check
  (AlgebraicGeometry.Scheme.Hom.smoothInCodimensionZero.exists_separable_normalizedFunctionFieldExtension :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [Scheme.Hom.FiniteType f]
      [Scheme.Nagata S] [IsIntegral S] [Scheme.Regular S],
      topologicalKrullDim S = 1 →
      (let qK := Scheme.FunctionFieldExtension.map S S.functionField
       let X_K := pullback f qK
       ∀ η : X_K, η ∈ genericPoints X_K →
         Scheme.Hom.ResidueField.IsSeparableOverSpec (pullback.snd f qK) η) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
          (_ : FiniteDimensional S.functionField L)
          (_ : Algebra.IsSeparable S.functionField L),
        let q := Scheme.FunctionFieldExtension.map S L
        let T := q.normalization
        let t : T ⟶ S := q.fromNormalization
        let X_T := pullback f t
        let Y := X_T.normalization
        let ν : Y ⟶ X_T := X_T.normalizationTo
        let g : Y ⟶ T := ν ≫ pullback.snd f t
        g.smoothInCodimensionZero)
