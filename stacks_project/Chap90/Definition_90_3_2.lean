module

public import stacks_project.Chap90.Definition_90_3_2_SmallExtension

/-!
# Small extensions

A morphism in the base category is a small extension when it is surjective
and its kernel is a nonzero principal ideal annihilated by the source maximal
ideal.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- Definition 90.3.2: a morphism `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k` is a small
extension if and only if it is surjective and `RingHom.ker f.hom.toRingHom` is a nonzero
principal ideal annihilated by `maximalIdeal B.carrier`. -/
@[stacks 06GD]
theorem isSmallExtension_iff {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsSmallExtension f ↔
      Function.Surjective f.hom ∧
        (RingHom.ker f.hom.toRingHom).IsPrincipal ∧
        RingHom.ker f.hom.toRingHom ≠ ⊥ ∧
        maximalIdeal B.carrier * RingHom.ker f.hom.toRingHom = ⊥ := sorry

end ArtinianLocalAlgCat
