module

public import stacks_project.Chap90.Lemma_90_3_5_Cotangent
public import stacks_project.Chap90.Lemma_90_4_2_Cotangent

/-!
# Surjectivity criteria in the completed base category

A morphism in `CompleteLocalAlgCat Λ k` is surjective if and only if it is surjective
on cotangent spaces, if and only if it is surjective on the relative quotients by
`m_Λ · (-) + maximalIdeal ^ 2`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat
namespace Hom

/-- Lemma 90.4.2 (1): a morphism `f : R ⟶ S` in `CompleteLocalAlgCat Λ k` is surjective if and
only if the induced map `CotangentSpace.mapAlgHom f.hom` of cotangent spaces is surjective. -/
@[stacks 06GZ]
theorem surjective_iff_mapAlgHom {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    Function.Surjective f.hom ↔ Function.Surjective (CotangentSpace.mapAlgHom f.hom) :=
  sorry

/-- Lemma 90.4.2 (2): the induced cotangent-space map of `f : R ⟶ S` is surjective if and only
if the induced map `mapRelative f` of relative quotients
`maximalIdeal ⧸ (m_Λ · (-) + maximalIdeal ^ 2)` is surjective. -/
@[stacks 06GZ]
theorem mapAlgHom_surjective_iff_mapRelative {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    Function.Surjective (CotangentSpace.mapAlgHom f.hom) ↔
      Function.Surjective (mapRelative f) :=
  sorry

/-- A morphism in `CompleteLocalAlgCat` is surjective if and only if the induced map of
relative quotients by `m_Λ · (-) + maximalIdeal ^ 2` is surjective. -/
theorem surjective_iff_mapRelative {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    Function.Surjective f.hom ↔ Function.Surjective (mapRelative f) :=
  sorry

end Hom
end CompleteLocalAlgCat
