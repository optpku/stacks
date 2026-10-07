module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.Separable
public import stacks_project.Chap90.Definition_90_3_2_SmallExtension
public import stacks_project.Chap90.Definition_90_3_9
public import stacks_project.Chap90.Lemma_90_3_4_Length
public import stacks_project.Chap90.Lemma_90_3_5_Cotangent
public import stacks_project.Chap90.Lemma_90_3_12_Comparison

/-!
# Essential-surjection and surjectivity criteria via Kähler maps

Lemma 90.3.12 records additional characterizations of surjectivity and of
essential surjectivity for a morphism in `C_Λ`, in terms of the induced maps
on images of `d_A` and on `k ⊗ Ω[· ⁄ Λ]`. When `k` is separable over
`residueImage Λ k`, essential surjectivity is equivalent to bijectivity of
`mapRelative`. A small extension fails to be essential if and only if it
splits in `C_Λ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing KaehlerDifferential
open scoped TensorProduct

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- Lemma 90.3.12 (1): for `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k`, the equivalent
conditions of Lemma 90.3.5 characterizing surjectivity of `f.hom` (namely
surjectivity of `CotangentSpace.mapAlgHom f.hom` and of `Hom.mapRelative f`)
are also equivalent to surjectivity of `Hom.conormalRangeMap f` and of
`Hom.kaehlerTensorMap f`. -/
@[stacks 06H0]
theorem surjective_tfae {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    List.TFAE [Function.Surjective f.hom, Function.Surjective (Hom.conormalRangeMap f),
      Function.Surjective (Hom.kaehlerTensorMap f)] :=
  sorry

/-- Surjectivity of a morphism in `ArtinianLocalAlgCat Λ k` is equivalent to
surjectivity of `Hom.conormalRangeMap f`. -/
theorem surjective_iff_conormalRangeMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    Function.Surjective f.hom ↔ Function.Surjective (Hom.conormalRangeMap f) :=
  sorry

/-- Surjectivity of a morphism in `ArtinianLocalAlgCat Λ k` is equivalent to
surjectivity of `Hom.kaehlerTensorMap f`. -/
theorem surjective_iff_kaehlerTensorMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    Function.Surjective f.hom ↔ Function.Surjective (Hom.kaehlerTensorMap f) :=
  sorry

/-- Lemma 90.3.12 (2): for `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k`, the following
are equivalent: `f` is an essential surjection, `Hom.conormalRangeMap f` is
bijective, and `Hom.kaehlerTensorMap f` is bijective. -/
@[stacks 06H0]
theorem isEssentialSurjection_tfae {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    List.TFAE [IsEssentialSurjection f, Function.Bijective (Hom.conormalRangeMap f),
      Function.Bijective (Hom.kaehlerTensorMap f)] :=
  sorry

/-- A morphism in `ArtinianLocalAlgCat Λ k` is an essential surjection if and only
if `Hom.conormalRangeMap f` is bijective. -/
theorem isEssentialSurjection_iff_bijective_conormalRangeMap
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔ Function.Bijective (Hom.conormalRangeMap f) :=
  sorry

/-- A morphism in `ArtinianLocalAlgCat Λ k` is an essential surjection if and only
if `Hom.kaehlerTensorMap f` is bijective. -/
theorem isEssentialSurjection_iff_bijective_kaehlerTensorMap
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔ Function.Bijective (Hom.kaehlerTensorMap f) :=
  sorry

/-- Lemma 90.3.12 (3): if `k` is separable over `residueImage Λ k`, then `f : B ⟶ A`
in `ArtinianLocalAlgCat Λ k` is an essential surjection if and only if
`Hom.mapRelative f` is bijective. -/
@[stacks 06H0]
theorem isEssentialSurjection_iff_bijective_mapRelative
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    IsEssentialSurjection f ↔ Function.Bijective (Hom.mapRelative f) :=
  sorry

/-- Lemma 90.3.12 (4): if `f : B ⟶ A` is a small extension in
`ArtinianLocalAlgCat Λ k`, then `f` is not an essential surjection if and only if
there exists a section `s : A ⟶ B` with `s ≫ f = 𝟙 A`. -/
@[stacks 06H0]
theorem not_isEssentialSurjection_iff_exists_section
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f] :
    ¬ IsEssentialSurjection f ↔ ∃ s : A ⟶ B, s ≫ f = 𝟙 A :=
  sorry

end ArtinianLocalAlgCat
