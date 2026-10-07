module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.TensorHom.Splitting
public import ReasLib.LinearAlgebra.UniversallyInjective.CharacterModule

@[expose] public section

open CategoryTheory

universe u

namespace CharacterModule.TensorHom

/-- Universal injectivity of a module morphism makes the induced morphism between
the curried character-tensor functors a split epimorphism. -/
theorem isSplitEpi_rightFunctor_map_of_universallyInjective :
    ∀ (R : Type u) [CommRing R] {M N : ModuleCat.{u} R} (f : M ⟶ N),
      LinearMap.UniversallyInjective.{u, u, u, u} f.hom →
        IsSplitEpi ((rightFunctor R).map f.op) := sorry

end CharacterModule.TensorHom
