module

public import ReasLib.CategoryTheory.Sites.Family.Covering
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering

/-!
# Scheme refinements of fpqc coverings of algebraic spaces

An fpqc covering family of an algebraic space admits an fpqc refinement whose
sources are schemes over the base.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 73.9.5: let `S` be a scheme and let `X` be an algebraic space over
`S`. If `𝒰 = {f_i : X_i ⟶ X}` is an fpqc covering of `X`, then there exists a
refinement `𝒱 = {g_j : ofOver (T j) ⟶ X}` of `𝒰` which is an fpqc covering
and such that each `T j` is a scheme over `S`. -/
@[stacks 0419]
theorem exists_schemeRefinement {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} (family : ι → Over X) (hfamily : FpqcCovering family) :
    ∃ (J : Type v) (T : J → Over S) (g : ∀ j, ofOver (T j) ⟶ X),
      FpqcCovering (fun j ↦ Over.mk (g j)) ∧
        Refines (ofArrows (fun j ↦ ofOver (T j)) g)
          (ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
