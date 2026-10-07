module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.PseudoCoherent.Module
import StacksCheckRecall

/-!
# Lemma 15.65.13

Lemma 15.65.13 (Stacks `066C`) is the degree-zero specialization of derived scalar extension.
The reusable owner accepts the explicit flat ring homomorphism from the source statement.

@stack 066C
-/

@[expose] public section

open CategoryTheory

universe u v w

/- Lemma 15.65.13 (1): flat scalar extension preserves `m`-pseudo-coherent modules. -/
@[stacks 066C "Lemma 15.65.13 (1)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (σ : A →+* B) (hσ : σ.Flat) {M : ModuleCat.{w, u} A} {m : ℤ}
    (hM : M.IsMPseudoCoherent m) ↦
  (ModuleCat.IsMPseudoCoherent.extension_of_flat hM σ hσ :
    ((ModuleCat.extendScalars σ).obj M).IsMPseudoCoherent m)

/- Lemma 15.65.13 (2): flat scalar extension preserves pseudo-coherent modules. -/
@[stacks 066C "Lemma 15.65.13 (2)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (σ : A →+* B) (hσ : σ.Flat) {M : ModuleCat.{w, u} A}
    (hM : M.IsPseudoCoherent) ↦
  (ModuleCat.IsPseudoCoherent.extension_of_flat hM σ hσ :
    ((ModuleCat.extendScalars σ).obj M).IsPseudoCoherent)

#check @ModuleCat.IsMPseudoCoherent.extension_of_flat
#check @ModuleCat.IsPseudoCoherent.extension_of_flat
