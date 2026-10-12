/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_3_5_Cotangent

/-!
# Surjectivity criteria in the base category

A morphism in `ArtinianLocalAlgCat Λ k` is surjective if and only if it is surjective
on cotangent spaces, if and only if it is surjective on the relative quotients by
`m_Λ · (-) + maximalIdeal ^ 2`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat
namespace Hom

/-- Lemma 90.3.5 (1): a morphism `f : A ⟶ B` in `ArtinianLocalAlgCat Λ k` is surjective if and
only if the induced map `CotangentSpace.mapAlgHom f.hom` of cotangent spaces is surjective. -/
@[stacks 06S3]
theorem surjective_iff_mapAlgHom {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Function.Surjective f.hom ↔ Function.Surjective (CotangentSpace.mapAlgHom f.hom) :=
  sorry

/-- Lemma 90.3.5 (2): the induced cotangent-space map of `f : A ⟶ B` is surjective if and only
if the induced map `mapRelative f` of relative quotients
`maximalIdeal ⧸ (m_Λ · (-) + maximalIdeal ^ 2)` is surjective. -/
@[stacks 06S3]
theorem mapAlgHom_surjective_iff_mapRelative {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Function.Surjective (CotangentSpace.mapAlgHom f.hom) ↔
      Function.Surjective (mapRelative f) :=
  sorry

/-- A morphism in `ArtinianLocalAlgCat` is surjective if and only if the induced map of
relative quotients by `m_Λ · (-) + maximalIdeal ^ 2` is surjective. -/
theorem surjective_iff_mapRelative {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Function.Surjective f.hom ↔ Function.Surjective (mapRelative f) :=
  sorry

end Hom
end ArtinianLocalAlgCat
