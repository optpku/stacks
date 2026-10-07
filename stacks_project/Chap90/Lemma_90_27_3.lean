module

public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_10_1_DualNumber

/-!
# Endomorphisms of prorepresentable functors with invertible differential

If `U : ArtinianLocalAlgCat Λ k ⥤ Type u` is prorepresentable, an endomorphism
whose dual-number component is bijective is itself an isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Lemma 90.27.3: if `U : ArtinianLocalAlgCat Λ k ⥤ Type u` is prorepresentable and
`φ : U ⟶ U` is a morphism such that `dφ : TU → TU` is an isomorphism, then `φ` is an
isomorphism. Here `TU` is `U.obj (ArtinianLocalAlgCat.dualNumber Λ k)` and `dφ` is the
component `φ.app (ArtinianLocalAlgCat.dualNumber Λ k)`. -/
@[stacks 06KP]
theorem isIso_of_bijective_tangentSpace {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    [IsProrepresentable U] (φ : U ⟶ U)
    (hφ : Function.Bijective (φ.app (ArtinianLocalAlgCat.dualNumber Λ k))) :
    IsIso φ := sorry

end CategoryTheory.Functor
