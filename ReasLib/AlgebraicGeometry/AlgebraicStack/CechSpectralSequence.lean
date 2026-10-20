/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cech.SpectralSequence
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Covering.FromLifts

/-!
# Cohomology of algebraic stacks via a relative Čech nerve

A smooth surjective 1-morphism of algebraic stacks that is representable by
algebraic spaces computes étale cohomology of an abelian étale sheaf from the
relative Čech nerve. The same holds in the fppf topology for a surjective flat
morphism locally of finite presentation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic
stacks. Let `F` be an abelian étale sheaf on `𝒳`. Assume that `f` is
representable by algebraic spaces, surjective, and smooth. Then there is a
spectral sequence `E₁^{p, q} = H^q_étale(𝒰_p, f_p⁻¹ F) ⇒ H^{p+q}_étale(𝒳, F)`. -/
@[stacks 06XJ]
theorem exists_etaleRelativeCechSpectralSequence [AlgebraicStack U]
    [AlgebraicStack X] (f : U ⟶ X)
    (F : Sheaf (X.etaleTopology) AddCommGrpCat.{u + 1})
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Smooth f]
    [HasSheafify (X.associatedTopology StandardTopology.etale) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology StandardTopology.etale) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f StandardTopology.etale p)
      AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1}
      (Sheaf (relativeCechSite f StandardTopology.etale p) AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechPageOne f StandardTopology.etale F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (X.associatedTopology StandardTopology.etale) n).obj F) :=
  sorry

/-- Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic
stacks. Let `F` be an abelian sheaf on `𝒳`. Assume that `f` is representable
by algebraic spaces, surjective, flat, and locally of finite presentation.
Then there is a spectral sequence
`E₁^{p, q} = H^q_fppf(𝒰_p, f_p⁻¹ F) ⇒ H^{p+q}_fppf(𝒳, F)`. -/
@[stacks 06XJ]
theorem exists_fppfRelativeCechSpectralSequence [AlgebraicStack U]
    [AlgebraicStack X] (f : U ⟶ X)
    (F : Sheaf (X.fppfTopology) AddCommGrpCat.{u + 1})
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    [HasSheafify (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f StandardTopology.fppf p)
      AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1}
      (Sheaf (relativeCechSite f StandardTopology.fppf p) AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechPageOne f StandardTopology.fppf F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (X.associatedTopology StandardTopology.fppf) n).obj F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
