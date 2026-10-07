module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.GradedPieces
public import stacks_project.Chap69.Lemma_69_6_3_Comparison
public import stacks_project.Chap69.Lemma_69_6_3_DerivedSections
public import stacks_project.Chap69.Lemma_69_6_3_SpectralSequence

/-!
# Lemma 69.6.3

Canonical comparison from the alternating Čech complex of a surjective étale morphism
of algebraic spaces to derived global sections, and the associated first-quadrant
Ext spectral sequence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open HomologicalComplex HomologicalComplex₂ Opposite ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Lemma 69.6.3 (1): Let `S` be a scheme. Let `f : U ⟶ X` be a surjective étale morphism of
algebraic spaces over `S`. Let `F` be an object of `Ab(X_étale)`. There is a canonical map
`Čech_alt(f, F) ⟶ RΓ(X, F)` in `D(Ab)`, constructed as the composition of
`Čech_alt(f, F) ⟶ Tot(Hom(K^•, I^•))` with the inverse of the quasi-isomorphism
`Γ(X, I^•) ⟶ Tot(Hom(K^•, I^•))`. The target is the injective model of `RΓ(X, F)`. -/
@[stacks 0725]
noncomputable def alternatingCechToRGamma {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    [HasDerivedCategory AddCommGrpCat.{u + 1}] :
    DerivedCategory.Q.obj ((alternatingCechComplex f F).extend embeddingUpNat) ⟶
      DerivedCategory.Q.obj (injectiveGammaComplex F) :=
  DerivedCategory.Q.map (alternatingCechToTotal f F) ≫
    CategoryTheory.inv (DerivedCategory.Q.map (injectiveGammaToTotal f F))

/-- The canonical map to derived sections is `Čech_alt ⟶ Tot` followed by the inverse of
`Γ(X, I^•) ⟶ Tot`. -/
theorem alternatingCechToRGamma_comp_injectiveGammaToTotal {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    [HasDerivedCategory AddCommGrpCat.{u + 1}] :
    alternatingCechToRGamma f F ≫ DerivedCategory.Q.map (injectiveGammaToTotal f F) =
      DerivedCategory.Q.map (alternatingCechToTotal f F) :=
  sorry

/-- Lemma 69.6.3 (2): Let `S` be a scheme. Let `f : U ⟶ X` be a surjective étale morphism of
algebraic spaces over `S`. Let `F` be an object of `Ab(X_étale)`. There is a spectral sequence
with `E₁`-page `E₁^{p,q} = Ext^q(K^p, F)` converging to `H^{p+q}(X, F)`, where
`K^p = ∧^{p+1}(f_! ℤ̲)`. It is the first-quadrant reindexing of the spectral sequence
associated to the first filtration of `Hom(K^•, I^•)`. -/
@[stacks 0725]
noncomputable def alternatingCechSpectralSequence {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1 :=
  firstQuadrantSequence (associatedFirstFiltrationSequence f F).sequence
    (associatedFirstFiltrationSequence_supported f F)

/-- The Hom bicomplex of a surjective étale morphism has the first-filtration graded-piece
comparisons identifying each column with the corresponding signed vertical Hom-complex. -/
theorem homBicomplex_firstGradedPieceComparisons {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    First.GradedPiece.Comparisons (homBicomplex f F) :=
  sorry

/-- The `E₁`-page is `Ext^q_{Ab(X_étale)}(K^p, F)`, where
`K^p = (koszulComplex f).X p = ∧^{p+1}(f_! ℤ̲)`. -/
theorem alternatingCechSpectralSequence_pageOne_ext {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (p q : ℕ) :
    IsIsomorphic (((alternatingCechSpectralSequence f F).page 1 le_rfl).X (p, q))
      (AddCommGrpCat.of (Abelian.Ext ((koszulComplex f).X p) F q)) :=
  sorry

/-- The spectral sequence converges to `H^{p+q}(X, F)`. -/
theorem alternatingCechSpectralSequence_convergesTo {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    CohomologicalSpectralSequenceNat.ConvergesTo (alternatingCechSpectralSequence f F)
      (fun n ↦ (Sheaf.functorH (smallEtaleTopology X) n).obj F) :=
  sorry

/-- The spectral sequence abuts to `H^{p+q}(X, F)`, as a corollary of convergence. -/
theorem alternatingCechSpectralSequence_abutsTo {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] :
    CohomologicalSpectralSequenceNat.AbutsTo (alternatingCechSpectralSequence f F)
      (fun n ↦ (Sheaf.functorH (smallEtaleTopology X) n).obj F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
