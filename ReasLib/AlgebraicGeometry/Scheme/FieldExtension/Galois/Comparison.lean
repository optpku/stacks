/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.ConnectedComponents
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.IrreducibleComponents

/-!
# Comparisons between separable-closure base changes

This leaf owns the comparison maps attached to a chosen embedding of separable closures.
The constructions are stated for a morphism to `Spec k`, rather than for an `Over` wrapper,
so they can be reused by connected components, irreducible components, and later descent APIs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.SepClosure

/-- Under separable-closure hypotheses, the comparison map on connected components is bijective. -/
theorem map_bijective
    (k k' ksep ksep' : Type u) [Field k] [Field k'] [Field ksep] [Field ksep']
    [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [IsSepClosure k ksep]
    [IsSepClosure k' ksep'] [Algebra k ksep'] [IsScalarTower k k' ksep']
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) (i : ksep →ₐ[k] ksep') :
    Function.Bijective
      (FieldExtension.Comparison.connectedComponentsMap f i) := sorry

/-- The restriction homomorphism `Gal(ksep' / k') → Gal(ksep / k)` attached to an embedding. -/
noncomputable abbrev restrict
    (k k' ksep ksep' : Type u) [Field k] [Field k'] [Field ksep] [Field ksep']
    [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [IsSepClosure k ksep]
    [IsSepClosure k' ksep'] [Algebra k ksep'] [IsScalarTower k k' ksep']
    (i : ksep →ₐ[k] ksep') : Gal(ksep'/k') →* Gal(ksep/k) :=
  -- Local instance justification (noncanonical choice): induced by the chosen embedding `i`.
  letI : Algebra ksep ksep' := i.toRingHom.toAlgebra
  IntermediateField.restrictRestrictAlgEquivMapHom k ksep k' ksep'

/-- The `Spec ksep'` automorphism induced by a `k'`-Galois element, viewed over `Spec k`. -/
noncomputable abbrev baseAut
    (k k' ksep' : Type u) [Field k] [Field k'] [Field ksep']
    [Algebra k k'] [Algebra k' ksep'] [Algebra k ksep']
    [IsScalarTower k k' ksep'] (σ : Gal(ksep'/k')) :
    Spec (of ksep') ⟶ Spec (of ksep') :=
  Spec.map (ofHom ((σ.restrictScalars k).symm : ksep' →+* ksep'))

/-- The prime-closure Galois automorphism lies over `Spec k`. -/
theorem baseAut_over
    (k k' ksep' : Type u) [Field k] [Field k'] [Field ksep']
    [Algebra k k'] [Algebra k' ksep']
    [Algebra k ksep'] [IsScalarTower k k' ksep']
    (σ : Gal(ksep'/k')) :
    baseAut k k' ksep' σ ≫
        FieldExtension.specMap k ksep' =
      FieldExtension.specMap k ksep' := sorry

/-- The pullback endomorphism induced by a Galois element of the larger separable closure. -/
noncomputable abbrev pullback
    (k k' ksep' : Type u) [Field k] [Field k'] [Field ksep']
    [Algebra k k'] [Algebra k' ksep']
    [Algebra k ksep'] [IsScalarTower k k' ksep']
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) (σ : Gal(ksep'/k')) :
    FieldExtension.baseChange k ksep' f ⟶ FieldExtension.baseChange k ksep' f :=
    FieldExtension.Equivariance.map f
    (baseAut k k' ksep' σ)
    (baseAut_over k k' ksep' σ)

/-- The comparison map on connected components intertwines the Galois actions via restriction. -/
theorem map_commutes_galois
    (k k' ksep ksep' : Type u) [Field k] [Field k'] [Field ksep] [Field ksep']
    [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [IsSepClosure k ksep]
    [IsSepClosure k' ksep'] [Algebra k ksep'] [IsScalarTower k k' ksep']
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) (i : ksep →ₐ[k] ksep')
    (σ : Gal(ksep'/k')) (C : ConnectedComponents (FieldExtension.baseChange k ksep' f)) :
    FieldExtension.Comparison.connectedComponentsMap f i
        (Continuous.connectedComponentsMap
          ((pullback k k' ksep' f σ).continuous) C) =
      restrict k k' ksep ksep' i σ •
        FieldExtension.Comparison.connectedComponentsMap f i C := sorry

/-- The induced equivalence on irreducible components for a chosen separable-closure embedding. -/
noncomputable def componentsEquiv
    (k k' ksep ksep' : Type u) [Field k] [Field k'] [Field ksep] [Field ksep']
    [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [IsSepClosure k ksep]
    [IsSepClosure k' ksep'] [Algebra k ksep'] [IsScalarTower k k' ksep']
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) (i : ksep →ₐ[k] ksep') :
    irreducibleComponents (FieldExtension.baseChange k' ksep'
        (FieldExtension.toBase k k' f)) ≃
      irreducibleComponents (FieldExtension.baseChange k ksep f) :=
  let sourceIso := Scheme.AffineBaseChange.iteratedIso k k' ksep' f
  let sourceEquiv := (Scheme.homeoOfIso sourceIso).irreducibleComponentsEquiv
  -- Local instance justification (proof-local temporary data): `ksep` is separably closed by
  -- the first separable-closure hypothesis for this comparison equivalence.
  letI : IsSepClosed ksep := IsSepClosure.sep_closed k
  -- Local instance justification (proof-local temporary data): `ksep'` is separably closed by
  -- the second separable-closure hypothesis for this comparison equivalence.
  letI : IsSepClosed ksep' := IsSepClosure.sep_closed k'
  -- Local instance justification (noncanonical choice): induced by the chosen embedding `i`.
  letI : Algebra ksep ksep' := i.toRingHom.toAlgebra
  let directIso := Scheme.AffineBaseChange.iteratedIso k ksep ksep' f
  let iteratedToDirect := (Scheme.homeoOfIso directIso).irreducibleComponentsEquiv
  let baseChangeEquiv :=
    FieldExtension.Irreducible.componentsEquiv_of_isSepClosed
      ksep ksep' (FieldExtension.toBase k ksep f)
  sourceEquiv.trans (iteratedToDirect.symm.trans baseChangeEquiv)

/-- The comparison equivalence intertwines the opposite-Galois actions via restriction. -/
theorem equiv_commutes_galois
    (k k' ksep ksep' : Type u) [Field k] [Field k'] [Field ksep] [Field ksep']
    [Algebra k k'] [Algebra k ksep] [Algebra k' ksep'] [IsSepClosure k ksep]
    [IsSepClosure k' ksep'] [Algebra k ksep'] [IsScalarTower k k' ksep']
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) (i : ksep →ₐ[k] ksep')
    (σ : Gal(ksep'/k'))
    (Tbar : irreducibleComponents (FieldExtension.baseChange k' ksep'
      (FieldExtension.toBase k k' f))) :
    componentsEquiv k k' ksep ksep' f i
        (MulOpposite.op σ • Tbar) =
      MulOpposite.op (restrict k k' ksep ksep' i σ) •
        componentsEquiv k k' ksep ksep' f i Tbar := sorry

end FieldExtension.Galois.SepClosure

end AlgebraicGeometry
