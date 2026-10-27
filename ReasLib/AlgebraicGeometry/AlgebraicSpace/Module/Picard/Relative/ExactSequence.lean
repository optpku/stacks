/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.WithSection

/-!
# Exactness and splitting of the relative Picard sequence

If the canonical structure-sheaf map is an isomorphism after every scheme base
change, pullback on Picard groups is injective and its image is the kernel of
the map to the relative Picard sheaf. A chosen section makes this map
surjective, and pullback along the base-changed section retracts Picard
pullback independently of the structure-sheaf hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The canonical map from the Picard group of a scheme base change to the
relative Picard sheaf is the component of the sheafification unit. -/
def toFunctor (f : X ⟶ B) (σ : SchemesOver B) :
    (fiber f σ).PicardGroup → (picardFunctor f).obj.obj (op σ) :=
  ((sheafificationAdjunction (SchemesOver.fppfTopology B) (Type (u + 1))).unit.app
    (presheaf f)).app (op σ)

/-- The canonical comparison map sends a Picard class to its image under the
sheafification unit of the relative Picard presheaf. -/
theorem toFunctor_apply (f : X ⟶ B) (σ : SchemesOver B)
    (L : (fiber f σ).PicardGroup) :
    toFunctor f σ L =
      ((sheafificationAdjunction (SchemesOver.fppfTopology B) (Type (u + 1))).unit.app
        (presheaf f)).app (op σ) L := sorry

/-- If the canonical structure-sheaf map is an isomorphism after every scheme
base change, Picard pullback is injective and its image consists exactly of the
classes mapping to the basepoint of the relative Picard sheaf. -/
theorem picardSequence_exact (f : X ⟶ B)
    (h_iso : ∀ σ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f σ)))
    (σ : SchemesOver B) :
    Function.Injective (picardPullback (fiberToBase f σ)) ∧
      ∀ L : (fiber f σ).PicardGroup,
        toFunctor f σ L = toFunctor f σ 0 ↔
          L ∈ Set.range (picardPullback (fiberToBase f σ)) := sorry

/-- If a morphism has a chosen section and the canonical structure-sheaf map
is an isomorphism after every scheme base change, the canonical map from the
Picard group of each base change to the relative Picard sheaf is surjective. -/
theorem picardSequence_surjective (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (h_iso : ∀ τ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f τ)))
    (τ : SchemesOver B) :
    Function.Surjective (toFunctor f τ) := sorry

/-- Pullback along the base change of a chosen section is a left inverse of
Picard pullback along the fibre projection. -/
theorem picardSequence_split (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (τ : SchemesOver B) :
    Function.LeftInverse (Picard.WithSection.sectionPicard f σ hσ τ)
      (picardPullback (fiberToBase f τ)) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
