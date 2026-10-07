module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap96.Lemma_96_19_11
public import stacks_project.Chap96.Lemma_96_19_12
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Relative Čech spectral sequences for higher direct images

A smooth surjective 1-morphism of algebraic stacks that is representable by
algebraic spaces computes étale higher direct images of an abelian sheaf or
sheaf of modules from the relative Čech nerve. The same holds in the fppf
topology for a surjective flat morphism locally of finite presentation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}

/-- Proposition 96.21.1 (1): Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable
1-morphisms of algebraic stacks. Let `F` be an abelian étale sheaf on `𝒳`.
Assume that `f` is representable by algebraic spaces, surjective, and smooth.
Then there is a spectral sequence
`E₁^{p, q} = R^q (g ∘ f_p)_* f_p⁻¹ F ⇒ R^{p+q} g_* F` in `Ab(𝒴_étale)`,
with higher direct images computed in the étale topology. -/
@[stacks 072G]
theorem exists_etaleRelativeCechPushforwardSpectralSequence
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : U ⟶ X) (g : X ⟶ Y)
    (F : Sheaf (X.associatedTopology StandardTopology.etale) AddCommGrpCat.{u + 1})
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Smooth f]
    [HasSheafify (X.associatedTopology StandardTopology.etale) AddCommGrpCat.{u + 1}]
    [HasSheafify (Y.associatedTopology StandardTopology.etale) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions
      (Sheaf (X.associatedTopology StandardTopology.etale) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f StandardTopology.etale p)
      AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasInjectiveResolutions
      (Sheaf (relativeCechSite f StandardTopology.etale p) AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat
        (Sheaf (Y.associatedTopology StandardTopology.etale) AddCommGrpCat.{u + 1}) 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechPushforwardPageOne f g StandardTopology.etale F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ higherDirectImage g StandardTopology.etale F n) :=
  sorry

/-- Proposition 96.21.1 (2): Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable
1-morphisms of algebraic stacks. Let `F` be a sheaf of modules on
`𝒳_étale`. Assume that `f` is representable by algebraic spaces, surjective,
and smooth. Then there is a spectral sequence
`E₁^{p, q} = R^q (g ∘ f_p)_* f_p⁻¹ F ⇒ R^{p+q} g_* F` in
`Mod(𝒴_étale, 𝒪_𝒴)`. -/
@[stacks 072G]
theorem exists_etaleRelativeCechModulePushforwardSpectralSequence
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : U ⟶ X) (g : X ⟶ Y)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X StandardTopology.etale))
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Smooth f]
    [HasInjectiveResolutions
      (SheafOfModules.{u + 1} (associatedStructureSheaf X StandardTopology.etale))]
    [∀ p : ℕ, HasInjectiveResolutions
      (SheafOfModules.{u + 1}
        (associatedStructureSheaf
          (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) StandardTopology.etale))] :
    ∃ (E : CohomologicalSpectralSequenceNat
        (SheafOfModules.{u + 1}
          (associatedStructureSheaf Y StandardTopology.etale)) 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechModulePushforwardPageOne f g StandardTopology.etale F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ associatedModuleHigherDirectImage g StandardTopology.etale F n) :=
  sorry

/-- Proposition 96.21.1 (3): Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable
1-morphisms of algebraic stacks. Let `F` be an abelian sheaf on `𝒳`. Assume
that `f` is representable by algebraic spaces, surjective, flat, and locally of
finite presentation. Then there is a spectral sequence
`E₁^{p, q} = R^q (g ∘ f_p)_* f_p⁻¹ F ⇒ R^{p+q} g_* F` in `Ab(𝒴)`, with higher
direct images computed in the fppf topology. -/
@[stacks 072G]
theorem exists_fppfRelativeCechPushforwardSpectralSequence
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : U ⟶ X) (g : X ⟶ Y)
    (F : Sheaf (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1})
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    [HasSheafify (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1}]
    [HasSheafify (Y.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions
      (Sheaf (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f StandardTopology.fppf p)
      AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasInjectiveResolutions
      (Sheaf (relativeCechSite f StandardTopology.fppf p) AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat
        (Sheaf (Y.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1}) 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechPushforwardPageOne f g StandardTopology.fppf F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ higherDirectImage g StandardTopology.fppf F n) :=
  sorry

/-- Proposition 96.21.1 (4): Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable
1-morphisms of algebraic stacks. Let `F` be a sheaf of modules on `𝒪_𝒳`.
Assume that `f` is representable by algebraic spaces, surjective, flat, and
locally of finite presentation. Then there is a spectral sequence
`E₁^{p, q} = R^q (g ∘ f_p)_* f_p⁻¹ F ⇒ R^{p+q} g_* F` in `Mod(𝒪_𝒴)`, with
higher direct images computed in the fppf topology. -/
@[stacks 072G]
theorem exists_fppfRelativeCechModulePushforwardSpectralSequence
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : U ⟶ X) (g : X ⟶ Y)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X StandardTopology.fppf))
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    [HasInjectiveResolutions
      (SheafOfModules.{u + 1} (associatedStructureSheaf X StandardTopology.fppf))]
    [∀ p : ℕ, HasInjectiveResolutions
      (SheafOfModules.{u + 1}
        (associatedStructureSheaf
          (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) StandardTopology.fppf))] :
    ∃ (E : CohomologicalSpectralSequenceNat
        (SheafOfModules.{u + 1}
          (associatedStructureSheaf Y StandardTopology.fppf)) 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechModulePushforwardPageOne f g StandardTopology.fppf F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ associatedModuleHigherDirectImage g StandardTopology.fppf F n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
