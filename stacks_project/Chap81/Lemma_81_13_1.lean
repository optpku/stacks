module

public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
public import stacks_project.Chap81.Lemma_81_13_1_Equalizer
public import stacks_project.Chap81.Lemma_81_13_1_Coequalizer

/-!
# Lemma 81.13.1

The kernel pair of a proper morphism of algebraic spaces over a locally
Noetherian base has a coequalizer in algebraic spaces, with finite universally
injective structure morphism and proper surjective source morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 81.13.1 (1): Let `S` be a scheme and `g : Y ⟶ X` a proper morphism of
algebraic spaces over `S` with `X` locally Noetherian. Write `R` for the kernel
pair `relation g` with projections `fst g` (Stacks `t`) and `snd g` (Stacks `s`).
Then `fromSource g : Y ⟶ space g` is a coequalizer of `snd g, fst g` in
`AlgebraicSpace S`, where `space g` is the relative spectrum of
`equalizerAlgebra g`. -/
@[stacks 0AGG]
theorem isCoequalizer (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g]
    {Z : AlgebraicSpace S} (φ : Y ⟶ Z) (h_equalizes : fst g ≫ φ = snd g ≫ φ) :
    ∃! ψ : space g ⟶ Z, fromSource g ≫ ψ = φ :=
  sorry

/-- Lemma 81.13.1 (2): the structure morphism `toTarget g : space g ⟶ X` is
finite. -/
@[stacks 0AGG, instance]
instance instIsFinite_toTarget (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    IsFinite (toTarget g) :=
  sorry

/-- Lemma 81.13.1 (3): the source morphism `fromSource g : Y ⟶ space g` is
proper. -/
@[stacks 0AGG, instance]
instance instProper_fromSource (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    Proper (fromSource g) :=
  sorry

/-- Lemma 81.13.1 (4): the source morphism `fromSource g : Y ⟶ space g` is
surjective. -/
@[stacks 0AGG, instance]
instance instSurjective_fromSource (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] : Surjective (fromSource g) :=
  sorry

/-- Lemma 81.13.1 (5): the structure morphism `toTarget g : space g ⟶ X` is
universally injective. -/
@[stacks 0AGG, instance]
instance instUniversallyInjective_toTarget (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] : UniversallyInjective (toTarget g) :=
  sorry

/-- Lemma 81.13.1 (6): if `g` is surjective, then `toTarget g : space g ⟶ X` is a
universal homeomorphism. -/
@[stacks 0AGG, instance]
instance instUniversalHomeomorphism_toTarget (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] [Surjective g] : UniversalHomeomorphism (toTarget g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer
