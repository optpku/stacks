module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Pointlike quasi-separated algebraic spaces

A quasi-separated algebraic space over a scheme that admits a surjective étale morphism from
the spectrum of a field is isomorphic to the spectrum of a finite separable extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.15.3: let `S` be a scheme, let `k` be a field, and let `X` be a quasi-separated
algebraic space over `S`. If there is a surjective étale morphism `Spec (CommRingCat.of k) ⟶ X`,
then `X` is isomorphic over `S` to `ofOver (Over.mk σ')` for a finite separable extension
`k / k'`. -/
@[stacks 03DZ]
theorem exists_iso_spec_finiteSeparable {S : Scheme.{u}} {k : Type u} [Field k]
    {X : AlgebraicSpace S} [IsQuasiSeparated X] (σ : Spec (CommRingCat.of k) ⟶ S)
    (f : yoneda.obj (Over.mk σ) ⟶ X.functorOfPoints)
    (hf_etale : (MorphismProperty.over (@Etale)).presheaf f)
    (hf_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k' k) (σ' : Spec (CommRingCat.of k') ⟶ S),
      FiniteDimensional k' k ∧ Algebra.IsSeparable k' k ∧
      Spec.map (CommRingCat.ofHom (algebraMap k' k)) ≫ σ' = σ ∧
      Nonempty (X ≅ ofOver (Over.mk σ')) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
