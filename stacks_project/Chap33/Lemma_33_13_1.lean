/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.CohenMacaulay

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.13.1 (1): let `X` be a locally Noetherian scheme over the field `k`, let `K / k`
be a finitely generated field extension, let `x ∈ X`, and let `x' ∈ X_{k'}` lie over `x`. Then
the local ring `𝒪_{X, x}` is Cohen-Macaulay if and only if the local ring
`𝒪_{X_{k'}, x'}` is Cohen-Macaulay. -/
@[stacks 045P] #check
  (AlgebraicGeometry.FieldExtension.CohenMacaulay.stalk_iff_of_essFiniteType.{u} :
    ∀ {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      [IsLocallyNoetherian X] [Algebra.EssFiniteType k K]
      (x : X) (x' : FieldExtension.baseChange k K f),
      FieldExtension.toSource k K f x' = x →
        (Module.CohenMacaulay ((Scheme.toLocallyRingedSpace X).presheaf.stalk x)
          ((Scheme.toLocallyRingedSpace X).presheaf.stalk x) ↔
          let _ : IsLocallyNoetherian (FieldExtension.baseChange k K f) :=
            (AlgebraicGeometry.Scheme.Hom.isLocallyNoetherian_iff_isLocallyNoetherian_pullback_fieldExtension
              (K := K) f).1 inferInstance
          Module.CohenMacaulay ((FieldExtension.baseChange k K f).presheaf.stalk x')
            ((FieldExtension.baseChange k K f).presheaf.stalk x')))

/- Lemma 33.13.1 (2): if `X` is locally of finite type over the field `k`, then for any field
extension `K / k`, any `x ∈ X`, and any `x' ∈ X_{K}` lying over `x`, the local ring
`𝒪_{X, x}` is Cohen-Macaulay if and only if the local ring `𝒪_{X_{k'}, x'}` is
Cohen-Macaulay. -/
@[stacks 045P] #check
  (AlgebraicGeometry.FieldExtension.CohenMacaulay.stalk_iff_of_locallyOfFiniteType :
    ∀ {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
      (x : X) (x' : FieldExtension.baseChange k K f),
      FieldExtension.toSource k K f x' = x →
        let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
        let _ : IsLocallyNoetherian (FieldExtension.baseChange k K f) :=
          LocallyOfFiniteType.isLocallyNoetherian (FieldExtension.toBase k K f)
        Module.CohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) ↔
          Module.CohenMacaulay ((FieldExtension.baseChange k K f).presheaf.stalk x')
            ((FieldExtension.baseChange k K f).presheaf.stalk x'))
