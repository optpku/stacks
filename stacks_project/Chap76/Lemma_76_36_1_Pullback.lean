module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_4_4_Pullback
public import stacks_project.Chap67.Lemma_67_8_4_QuasiCompact
public import stacks_project.Chap67.Lemma_67_9_7
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_48_4_Pullback

/-!
# Flat base change of relative normalization

Formation of the relative-normalization factorization of a universally closed
quasi-separated morphism of algebraic spaces commutes with flat base change:
the canonical comparison from the normalization of the pulled-back morphism to
the pullback of the normalization is a unique isomorphism of triangles.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- After flat base change, the relative normalization of the pulled-back
morphism is uniquely isomorphic to the pullback of the relative normalization,
compatibly with the maps from the pulled-back source and the structure
morphisms to the new base. -/
theorem existsUnique_isIso_normalizationPullback_of_flat
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] [Flat g] :
    ∃! h : normalization (pullback.snd f g) ⟶
        pullback (fromNormalization f) g,
      toNormalization (pullback.snd f g) ≫ h =
          pullbackToNormalization f g ∧
        h ≫ pullback.snd (fromNormalization f) g =
          fromNormalization (pullback.snd f g) ∧
        IsIso h :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
