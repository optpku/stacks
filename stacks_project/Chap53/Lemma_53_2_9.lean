/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Reduced.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.SmoothModels
import StacksCheckRecall

open CategoryTheory

universe u

namespace AlgebraicGeometry.NonsingularProjectiveModel.WithIso

/- Lemma 53.2.9 (1): if a geometrically irreducible curve `X` is proper over `k`, then every
nonsingular projective model of the reduced base change is isomorphic over `K` to the normalization of
`X_K`. -/
@[stacks 0BY4] #check
  (AlgebraicGeometry.NonsingularProjectiveModel.WithIso.isIsomorphic_normalizationBaseChange :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom] [IsProper X.hom]
    (Y : WithIso (FieldExtension.Reduced.baseChange k K X)),
    IsIsomorphic Y.curve (FieldExtension.Normalization.baseChange X K))

/- Lemma 53.2.9 (2): after a finite purely inseparable extension of the ground field, a
geometrically irreducible curve has a smooth nonsingular projective model of its reduced base
change. -/
@[stacks 0BY4] #check
  (AlgebraicGeometry.NonsingularProjectiveModel.WithIso.exists_smooth :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [GeometricallyIrreducible X.hom],
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (_ : FiniteDimensional k K) (_ : IsPurelyInseparable k K)
      (Y : WithIso (FieldExtension.Reduced.baseChange k K X)),
      Smooth Y.curve.hom)

/- Lemma 53.2.9 (3): if a nonsingular projective model `Y_K` of the reduced base change of a
geometrically irreducible curve is smooth, then the canonical map
`K → Γ(Y_K, 𝒪_{Y_K})` is bijective. -/
@[stacks 0BY4] #check
  (AlgebraicGeometry.NonsingularProjectiveModel.WithIso.globalSectionsMap_bijective_of_smooth :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom]
    (Y : WithIso (FieldExtension.Reduced.baseChange k K X))
    [Smooth Y.curve.hom],
    Function.Bijective (Scheme.Hom.globalSectionsMap Y.curve.hom))

/- Lemma 53.2.9 (4): in a commutative diagram of field extensions from `k` to `K`, `K'`, and
`Ω`, if the nonsingular projective models over `K` and `K'` are smooth, then their base changes
to `Ω` are both isomorphic to the model over `Ω`. -/
@[stacks 0BY4] #check
  (AlgebraicGeometry.NonsingularProjectiveModel.WithIso.baseChange_isIsomorphic :
    ∀ {k K K' Ω : Type u} [Field k] [Field K] [Field K'] [Field Ω]
    [Algebra k K] [Algebra k K'] [Algebra k Ω] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower k K Ω] [IsScalarTower k K' Ω]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom]
    (Y_K : WithIso (FieldExtension.Reduced.baseChange k K X))
    (Y_K' : WithIso (FieldExtension.Reduced.baseChange k K' X))
    (Y_Ω : WithIso (FieldExtension.Reduced.baseChange k Ω X))
    [Smooth Y_K.curve.hom] [Smooth Y_K'.curve.hom],
    IsIsomorphic Y_Ω.curve (FieldExtension.Over.baseChange K Ω Y_K.curve) ∧
      IsIsomorphic Y_Ω.curve (FieldExtension.Over.baseChange K' Ω Y_K'.curve))

end AlgebraicGeometry.NonsingularProjectiveModel.WithIso
