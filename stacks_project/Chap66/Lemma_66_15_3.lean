module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PointLike

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.15.3: Let `S` be a scheme, let `k` be a field, and let `X` be an algebraic
space over `S` admitting a surjective étale morphism `Spec(k) ⟶ X`. If `X` is
quasi-separated in the absolute sense, then `X` is isomorphic over `S` to `Spec(k')`,
where the covering field `k` is a finite separable extension of `k'`. The structure
morphism of `Spec(k)` factors through `Spec(k') ⟶ S` via the algebra-induced spectrum map. -/
@[stacks 03DZ] #check (AlgebraicGeometry.AlgebraicSpace.exists_iso_spec_finiteSeparable :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k]
    {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X] (σ : Spec (CommRingCat.of k) ⟶ S)
    (f : yoneda.obj (Over.mk σ) ⟶ X.functorOfPoints)
    (hf_etale : (MorphismProperty.over (@Etale)).presheaf f)
    (hf_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f),
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k' k) (σ' : Spec (CommRingCat.of k') ⟶ S),
      FiniteDimensional k' k ∧ Algebra.IsSeparable k' k ∧
      Spec.map (CommRingCat.ofHom (algebraMap k' k)) ≫ σ' = σ ∧
      Nonempty (X ≅ ofOver (Over.mk σ')))

end AlgebraicGeometry.AlgebraicSpace
