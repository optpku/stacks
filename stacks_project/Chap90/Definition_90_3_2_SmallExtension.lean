/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension

/-!
# Small extensions in the base category

A morphism in `ArtinianLocalAlgCat Λ k` is a small extension when it is
surjective and its kernel is a nonzero principal ideal annihilated by the
source maximal ideal.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

#check (ArtinianLocalAlgCat.maximalIdeal :
  ∀ B : ArtinianLocalAlgCat Λ k, Ideal B.carrier)

#check (ArtinianLocalAlgCat.IsSmallExtension :
  ∀ {B A : ArtinianLocalAlgCat Λ k}, (B ⟶ A) → Prop)

#check (ArtinianLocalAlgCat.isSmallExtension_iff :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    IsSmallExtension f ↔
      Function.Surjective f.toRingHom ∧
        (RingHom.ker f.toRingHom).IsPrincipal ∧
        RingHom.ker f.toRingHom ≠ ⊥ ∧
        maximalIdeal B * RingHom.ker f.toRingHom = ⊥)

namespace IsSmallExtension

variable {B A : ArtinianLocalAlgCat Λ k}

#check (ArtinianLocalAlgCat.IsSmallExtension.surjective :
  ∀ {f : B ⟶ A} [IsSmallExtension f], Function.Surjective f.toRingHom)

#check (ArtinianLocalAlgCat.IsSmallExtension.ker_isPrincipal :
  ∀ {f : B ⟶ A} [IsSmallExtension f], (RingHom.ker f.toRingHom).IsPrincipal)

#check (ArtinianLocalAlgCat.IsSmallExtension.ker_ne_bot :
  ∀ {f : B ⟶ A} [IsSmallExtension f], RingHom.ker f.toRingHom ≠ ⊥)

#check (ArtinianLocalAlgCat.IsSmallExtension.ker_annihilated :
  ∀ {f : B ⟶ A} [IsSmallExtension f], maximalIdeal B * RingHom.ker f.toRingHom = ⊥)

#check (ArtinianLocalAlgCat.IsSmallExtension.spec :
  ∀ (f : B ⟶ A) [IsSmallExtension f],
    Function.Surjective f.toRingHom ∧
      (RingHom.ker f.toRingHom).IsPrincipal ∧
      RingHom.ker f.toRingHom ≠ ⊥ ∧
      maximalIdeal B * RingHom.ker f.toRingHom = ⊥)

#check (ArtinianLocalAlgCat.IsSmallExtension.exists_generator :
  ∀ (f : B ⟶ A) [IsSmallExtension f],
    ∃ x : B.carrier, x ≠ 0 ∧
      RingHom.ker f.toRingHom = Ideal.span {x} ∧
      ∀ m ∈ maximalIdeal B, m * x = 0)

end IsSmallExtension

end ArtinianLocalAlgCat
