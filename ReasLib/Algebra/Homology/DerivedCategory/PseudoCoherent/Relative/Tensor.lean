module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Basic
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative pseudo-coherence under scalar extension

This leaf owns preservation of relative pseudo-coherence under derived extension along a
pseudo-coherent ring map, together with its flat degree-zero specialization.

@stack 067B
@stack 067C
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [(algebraMap A B).IsPseudoCoherentRingMap]

/-- Lemma 15.82.13 (1): derived extension along a pseudo-coherent ring map preserves relative
`m`-pseudo-coherence over the base. -/
@[stacks 067B "(1), derived extension preserves relative m-pseudo-coherence"]
theorem extension_of_isPseudoCoherentRingMap
    {K : DerivedCategory (ModuleCat A)} {m : ℤ}
    (hK : K.IsMPseudoCoherentRelativeTo R m) :
    let _ : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A B)
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A B)).obj K).IsMPseudoCoherentRelativeTo
      R m := sorry

end CategoryTheory.DerivedCategory.IsMPseudoCoherentRelativeTo

namespace CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [(algebraMap A B).IsPseudoCoherentRingMap]

/-- Lemma 15.82.13 (2): derived extension along a pseudo-coherent ring map preserves relative
pseudo-coherence over the base. -/
@[stacks 067B "(2), derived extension preserves relative pseudo-coherence"]
theorem extension_of_isPseudoCoherentRingMap
    {K : DerivedCategory (ModuleCat A)} (hK : K.IsPseudoCoherentRelativeTo R) :
    let _ : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A B)
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A B)).obj K).IsPseudoCoherentRelativeTo
      R := sorry

end CategoryTheory.DerivedCategory.IsPseudoCoherentRelativeTo

namespace CategoryTheory.ModuleCat.IsMPseudoCoherentRelativeTo

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [(algebraMap A B).IsPseudoCoherentRingMap]

/-- Lemma 15.82.14 (1): flat extension along a pseudo-coherent ring map preserves relative
`m`-pseudo-coherence of modules over the base. -/
@[stacks 067C "(1), flat extension preserves relative m-pseudo-coherence"]
theorem extension_of_flat_of_isPseudoCoherentRingMap
    {M : ModuleCat A} {m : ℤ} (hM : M.IsMPseudoCoherentRelativeTo R m)
    (hflat : (algebraMap A B).Flat) :
    let _ : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A B)
    ((ModuleCat.extendScalars (algebraMap A B)).obj M).IsMPseudoCoherentRelativeTo R m := sorry

end CategoryTheory.ModuleCat.IsMPseudoCoherentRelativeTo

namespace CategoryTheory.ModuleCat.IsPseudoCoherentRelativeTo

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [(algebraMap A B).IsPseudoCoherentRingMap]

/-- Lemma 15.82.14 (2): flat extension along a pseudo-coherent ring map preserves relative
pseudo-coherence of modules over the base. -/
@[stacks 067C "(2), flat extension preserves relative pseudo-coherence"]
theorem extension_of_flat_of_isPseudoCoherentRingMap
    {M : ModuleCat A} (hM : M.IsPseudoCoherentRelativeTo R)
    (hflat : (algebraMap A B).Flat) :
    let _ : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A B)
    ((ModuleCat.extendScalars (algebraMap A B)).obj M).IsPseudoCoherentRelativeTo R := sorry

end CategoryTheory.ModuleCat.IsPseudoCoherentRelativeTo
