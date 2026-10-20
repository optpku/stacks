module

public import Mathlib.CategoryTheory.Sites.LocallySurjective

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F G : Sheaf J (Type w)}

/-- Local injectivity of a morphism of sheaves is equivalent to injectivity on
each section type indexed by an object of the site. -/
theorem isLocallyInjective_iff_objectwiseInjective (φ : F ⟶ G) :
    IsLocallyInjective φ ↔
      ∀ U : C, Function.Injective (φ.hom.app (op U)) := sorry

/-- Local surjectivity of a morphism of sheaves is equivalent to every target
section having preimages after restriction along a covering sieve. -/
theorem isLocallySurjective_iff_exists_coveringSieve (φ : F ⟶ G) :
    IsLocallySurjective φ ↔
      ∀ (U : C) (s : G.obj.obj (op U)),
        ∃ S : Sieve U, S ∈ J U ∧
          ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
            ∃ t : F.obj.obj (op V),
              φ.hom.app (op V) t = G.obj.map f.op s := sorry

end CategoryTheory.Sheaf
