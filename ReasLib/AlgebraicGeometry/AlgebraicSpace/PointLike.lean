module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Pointlike quasi-separated algebraic spaces

An absolutely quasi-separated algebraic space admitting a surjective étale morphism from
`Spec(k)` is represented by `Spec(k')`, where `k / k'` is a finite separable extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An absolutely quasi-separated algebraic space over `S` admitting a surjective étale
morphism from `Spec(k)` is isomorphic over `S` to `Spec(k')`, where the covering field `k`
is a finite separable extension of `k'` and its structure morphism factors through
`Spec(k') ⟶ S` via the algebra-induced spectrum map. -/
theorem exists_iso_spec_finiteSeparable {S : Scheme.{u}} {k : Type u} [Field k]
    {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X] (σ : Spec (CommRingCat.of k) ⟶ S)
    (f : yoneda.obj (Over.mk σ) ⟶ X.functorOfPoints)
    (hf_etale : (MorphismProperty.over (@Etale)).presheaf f)
    (hf_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k' k) (σ' : Spec (CommRingCat.of k') ⟶ S),
      FiniteDimensional k' k ∧ Algebra.IsSeparable k' k ∧
      Spec.map (CommRingCat.ofHom (algebraMap k' k)) ≫ σ' = σ ∧
      Nonempty (X ≅ ofOver (Over.mk σ')) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
