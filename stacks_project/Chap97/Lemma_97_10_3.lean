module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap97.Lemma_97_10_3_Postcomp

/-!
# Étale covering of relative Hom

If `Z ⟶ B` is finite locally free and `X' ⟶ X` is étale over `B`, then
`Mor_B(Z, X') ⟶ Mor_B(Z, X)` is representable by algebraic spaces and étale,
and is surjective when `X' ⟶ X` is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- Lemma 97.10.3 (1): let `S` be a scheme and let `Z ⟶ B` and `X' ⟶ X ⟶ B` be
morphisms of algebraic spaces over `S`. If `X' ⟶ X` is étale and `Z ⟶ B` is
finite locally free, then `Mor_B(Z, X') ⟶ Mor_B(Z, X)` is representable by
algebraic spaces and étale. -/
@[stacks 05Y5]
theorem postcomp_etale {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X' X : Over B} (f : X' ⟶ X) [Etale f.left] [FiniteLocallyFree Z.hom]
    (U : Over S) (ξ : HomPair Z X U) :
    ∃ (F : AlgebraicSpace S) (p : F ⟶ ofOver U)
      (q : uliftSheaf F ⟶ homSheaf Z X'),
      Etale p ∧
        IsPullback q (uliftSheafMap p) (postcomp f)
          (ofPair ((overEquiv Z X U).symm ξ)) :=
  sorry

/-- Lemma 97.10.3 (2): if in addition `X' ⟶ X` is surjective, then
`Mor_B(Z, X') ⟶ Mor_B(Z, X)` is surjective. -/
@[stacks 05Y5]
theorem postcomp_surjective {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X' X : Over B} (f : X' ⟶ X) [Etale f.left] [FiniteLocallyFree Z.hom]
    [Surjective f.left] (U : Over S) (ξ : HomPair Z X U) :
    ∃ (F : AlgebraicSpace S) (p : F ⟶ ofOver U)
      (q : uliftSheaf F ⟶ homSheaf Z X'),
      Etale p ∧ Surjective p ∧
        IsPullback q (uliftSheafMap p) (postcomp f)
          (ofPair ((overEquiv Z X U).symm ξ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
