module

public import ReasLib.RingTheory.RingHom.SquareZero.Functoriality

/-!
# Functoriality of naive Ext¹ along algebra maps and coefficient maps

Postcomposition along a coefficient map M →ₗ[B] N, and the composite of
restriction of scalars along B → C with precomposition by NL_{B/A} → NL_{C/A},
act on the source Ext¹ cokernel `extOneNaiveCotangent`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra Algebra.Generators Algebra.Extension

namespace RingHom.SquareZeroExtension

section Precomp

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

#check (RingHom.SquareZeroExtension.extOneNaiveCotangent_precomp :
    (Generators.self A B).toExtension.Cotangent →ₗ[B]
      (Generators.self A C).toExtension.Cotangent)

#check (RingHom.SquareZeroExtension.extOneNaiveCotangent_precomp_apply :
    ∀ (x : (Generators.self A B).toExtension.Cotangent),
    extOneNaiveCotangent_precomp x =
      Cotangent.map
        (Hom.toExtensionHom (defaultHom (Generators.self A B) (Generators.self A C)))
        x)

end Precomp

section Map

variable {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

#check (RingHom.SquareZeroExtension.extOneNaiveCotangent_map :
    (M →ₗ[B] N) → extOneNaiveCotangent A B M → extOneNaiveCotangent A B N)

#check (RingHom.SquareZeroExtension.extOneNaiveCotangent_map_mk :
    ∀ (c : M →ₗ[B] N) (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] M),
    extOneNaiveCotangent_map c (extOneNaiveCotangent_mk A B M f) =
      extOneNaiveCotangent_mk A B N (c ∘ₗ f))

#check (RingHom.SquareZeroExtension.extOneNaiveCotangent_map_zero :
    ∀ (c : M →ₗ[B] N),
      extOneNaiveCotangent_map c (0 : extOneNaiveCotangent A B M) = 0)

end Map

section Comap

#check (RingHom.SquareZeroExtension.extOneNaiveCotangent_comap :
    ∀ (B : Type u) {A C N : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N],
    extOneNaiveCotangent A C N → extOneNaiveCotangent A B N)

#check (RingHom.SquareZeroExtension.extOneNaiveCotangent_comap_mk :
    ∀ (B : Type u) {A C N : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]
    (f : (Generators.self A C).toExtension.Cotangent →ₗ[C] N),
    extOneNaiveCotangent_comap B (extOneNaiveCotangent_mk A C N f) =
      extOneNaiveCotangent_mk A B N
        (LinearMap.restrictScalars B f ∘ₗ extOneNaiveCotangent_precomp))

#check (RingHom.SquareZeroExtension.extOneNaiveCotangent_comap_zero :
    ∀ (B : Type u) {A C N : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N],
    extOneNaiveCotangent_comap B (0 : extOneNaiveCotangent A C N) = 0)

end Comap

end SquareZeroExtension

end RingHom
