/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Embedding.Extend

/-! # Augmentations of naive cotangent complexes -/

@[expose] public section

open CategoryTheory
open DerivedCategory HomologicalComplex ComplexShape

noncomputable section

universe u v

namespace Algebra.Extension.NaiveCotangent

/-- The augmentation of an algebra presentation annihilates the cotangent differential. -/
theorem toKaehler_comp_d {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (P : Extension.{u} R A) :
    (complex P).d 1 0 ≫ ModuleCat.ofHom P.toKaehler = 0 :=
  sorry

end Algebra.Extension.NaiveCotangent

namespace Algebra.NaiveCotangent

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- The augmentation `NL{A⁄Λ} ⟶ Ω[A⁄Λ][0]` in the derived category, induced by
the `toKaehler` map of the self-presentation. -/
def naiveCotangentToKaehler :
    Algebra.naiveCotangentObject Λ A ⟶
      (singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A Ω[A⁄Λ]) :=
  DerivedCategory.Q.map
    (extendMap
        ((ChainComplex.toSingle₀Equiv (Algebra.naiveCotangent Λ A)
            (ModuleCat.of A Ω[A⁄Λ])).symm
          ⟨ModuleCat.ofHom (Generators.self Λ A).toExtension.toKaehler,
            Extension.NaiveCotangent.toKaehler_comp_d (Generators.self Λ A).toExtension⟩)
        embeddingDownNat ≫
      (extendSingleIso embeddingDownNat (ModuleCat.of A Ω[A⁄Λ]) (0 : ℕ) (0 : ℤ) rfl).hom)

end Algebra.NaiveCotangent
