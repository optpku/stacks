module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap76.Lemma_76_7_6_Comparison

/-!
# Relative differentials of a fibre product of algebraic spaces

The relative differentials of a fibre product of algebraic spaces are canonically the
direct sum of the pullbacks of the relative differentials of its two factors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.Product

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- The Lemma 76.7.6 comparison along the first projection square over `𝟙 B`, from
`p^* Ω_{X/B}` to `Ω_{X ×_B Y / B}`. -/
def fstComparison (f : X ⟶ B) (g : Y ⟶ B) :
    (Modules.pullback (pullback.fst f g)).obj (relativeDifferentials f) ⟶
      relativeDifferentials (pullback.snd f g ≫ g) :=
  Hom.Differentials.comparison (pullback.fst f g) (𝟙 B) f (pullback.snd f g ≫ g)
    (pullback.condition.trans (Category.comp_id _).symm)

/-- The Lemma 76.7.6 comparison along the second projection square over `𝟙 B`, from
`q^* Ω_{Y/B}` to `Ω_{X ×_B Y / B}`. -/
def sndComparison (f : X ⟶ B) (g : Y ⟶ B) :
    (Modules.pullback (pullback.snd f g)).obj (relativeDifferentials g) ⟶
      relativeDifferentials (pullback.snd f g ≫ g) :=
  Hom.Differentials.comparison (pullback.snd f g) (𝟙 B) g (pullback.snd f g ≫ g)
    (Category.comp_id _).symm

/-- The assembled map `p^* Ω_{X/B} ⊞ q^* Ω_{Y/B} ⟶ Ω_{X ×_B Y / B}` induced by the two
projection comparisons of Lemma 76.7.6. -/
def comparison (f : X ⟶ B) (g : Y ⟶ B) :
    ((Modules.pullback (pullback.fst f g)).obj (relativeDifferentials f) ⊞
      (Modules.pullback (pullback.snd f g)).obj (relativeDifferentials g)) ⟶
      relativeDifferentials (pullback.snd f g ≫ g) :=
  biprod.desc (fstComparison f g) (sndComparison f g)

/-- The first projection component is the canonical differential comparison of Lemma 76.7.6. -/
theorem fstComparison_isComparison (f : X ⟶ B) (g : Y ⟶ B) :
    IsComparison (pullback.fst f g) f (pullback.snd f g ≫ g) (fstComparison f g) :=
  sorry

/-- The second projection component is the canonical differential comparison of Lemma 76.7.6. -/
theorem sndComparison_isComparison (f : X ⟶ B) (g : Y ⟶ B) :
    IsComparison (pullback.snd f g) g (pullback.snd f g ≫ g) (sndComparison f g) :=
  sorry

/-- Restricting the product comparison to its first summand gives the first projection
comparison. -/
theorem inl_comparison (f : X ⟶ B) (g : Y ⟶ B) :
    biprod.inl ≫ comparison f g = fstComparison f g :=
  sorry

/-- Restricting the product comparison to its second summand gives the second projection
comparison. -/
theorem inr_comparison (f : X ⟶ B) (g : Y ⟶ B) :
    biprod.inr ≫ comparison f g = sndComparison f g :=
  sorry

/-- The canonical comparison from the direct sum of the pulled-back relative differentials of
the factors to the relative differentials of their fibre product is an isomorphism. -/
instance comparison_isIso (f : X ⟶ B) (g : Y ⟶ B) : IsIso (comparison f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.Product
