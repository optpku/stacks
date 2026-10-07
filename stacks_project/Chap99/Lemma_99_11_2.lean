module

public import stacks_project.Chap99.Lemma_99_11_2_IsoClasses
public import stacks_project.Chap99.Situation_99_11_1

/-!
# The Picard functor as sheafification of fibrewise isomorphism classes

Lemma 99.11.2 identifies `picardFunctor f` with the fppf sheafification of
the fibrewise isomorphism-class presheaf of `Picard.toSchemesOver f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PreRelation (schemesOverFppf)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.11.2: in Situation 99.11.1, `picardFunctor f` is the fppf
sheafification of `Functor.fiberIsoClassPresheaf (Picard.toSchemesOver f)`,
the functor sending a scheme `T` over `B` to isomorphism classes of objects
of the Picard fibre over `T`. That fibre is the category of invertible
sheaves on `X_T`, so this is the same sheafification as `T ↦ Pic(X_T)`. -/
@[stacks 0D26]
instance picardFunctor_sheafify_fiberIsoClasses (f : X ⟶ B) :
    IsIso ((presheafToSheaf (schemesOverFppf B) (Type (u + 1))).map
      (Picard.fiberIsoClassToPresheaf f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
