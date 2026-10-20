module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.EssentialSurjection.Criteria

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

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.3.12 (1): for `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k`, the equivalent
conditions of Lemma 90.3.5 characterizing surjectivity of `f.hom` (namely
surjectivity of `CotangentSpace.mapAlgHom f.hom` and of `Hom.mapRelative f`)
are also equivalent to surjectivity of `Hom.conormalRangeMap f` and of
`Hom.kaehlerTensorMap f`. -/
@[stacks 06H0] #check (ArtinianLocalAlgCat.surjective_tfae :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    List.TFAE [Function.Surjective f.hom,
      Function.Surjective (ArtinianLocalAlgCat.Hom.conormalRangeMap f),
      Function.Surjective (ArtinianLocalAlgCat.Hom.kaehlerTensorMap f)])

#check (ArtinianLocalAlgCat.surjective_iff_conormalRangeMap :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    Function.Surjective f.hom ↔
      Function.Surjective (ArtinianLocalAlgCat.Hom.conormalRangeMap f))

#check (ArtinianLocalAlgCat.surjective_iff_kaehlerTensorMap :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    Function.Surjective f.hom ↔
      Function.Surjective (ArtinianLocalAlgCat.Hom.kaehlerTensorMap f))

/- Lemma 90.3.12 (2): for `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k`, the following
are equivalent: `f` is an essential surjection, `Hom.conormalRangeMap f` is
bijective, and `Hom.kaehlerTensorMap f` is bijective. -/
@[stacks 06H0] #check (ArtinianLocalAlgCat.isEssentialSurjection_tfae :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    List.TFAE [ArtinianLocalAlgCat.IsEssentialSurjection f,
      Function.Bijective (ArtinianLocalAlgCat.Hom.conormalRangeMap f),
      Function.Bijective (ArtinianLocalAlgCat.Hom.kaehlerTensorMap f)])

#check (ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_conormalRangeMap :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    ArtinianLocalAlgCat.IsEssentialSurjection f ↔
      Function.Bijective (ArtinianLocalAlgCat.Hom.conormalRangeMap f))

#check (ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_kaehlerTensorMap :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    ArtinianLocalAlgCat.IsEssentialSurjection f ↔
      Function.Bijective (ArtinianLocalAlgCat.Hom.kaehlerTensorMap f))

/- Lemma 90.3.12 (3): if `k` is separable over `residueImage Λ k`, then `f : B ⟶ A`
in `ArtinianLocalAlgCat Λ k` is an essential surjection if and only if
`Hom.mapRelative f` is bijective. -/
@[stacks 06H0] #check (ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_mapRelative :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k],
    ArtinianLocalAlgCat.IsEssentialSurjection f ↔
      Function.Bijective (ArtinianLocalAlgCat.Hom.mapRelative f))

/- Lemma 90.3.12 (4): if `f : B ⟶ A` is a small extension in
`ArtinianLocalAlgCat Λ k`, then `f` is not an essential surjection if and only if
there exists a section `s : A ⟶ B` with `s ≫ f = 𝟙 A`. -/
@[stacks 06H0] #check (ArtinianLocalAlgCat.not_isEssentialSurjection_iff_exists_section :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [ArtinianLocalAlgCat.IsSmallExtension f],
    ¬ ArtinianLocalAlgCat.IsEssentialSurjection f ↔ ∃ s : A ⟶ B, s ≫ f = 𝟙 A)
