module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import ReasLib.CategoryTheory.Sites.Cech.Cohomology
public import ReasLib.CategoryTheory.Sites.Cech.Sheaf
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectral sequences for a Cech covering

This leaf owns the coefficient-natural spectral-sequence interface for one covering family.  The
page-two and abutment targets are named functors, so consumers do not need to unfold a chosen
filtered-complex or a Grothendieck-spectral-sequence realization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w z v u

namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ι : Type w} [HasFiniteProducts (Over U)]

/-- The `E₂`-page target: Cech degree-`p` cohomology with coefficients in the degree-`q`
cohomology presheaf of a sheaf. -/
@[stacks 03AZ "Cech spectral-sequence page-two target"]
abbrev pageTwoFunctor (J : GrothendieckTopology C) (U : C)
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U)
    [HasProducts.{w} AddCommGrpCat.{z}]
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{v})] (p q : ℕ) :
    Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{z} :=
  Sheaf.cohomologyPresheafFunctor.{z, v, u} J q ⋙
    (cohomologyFunctor U family p).obj

/-- The page-two target evaluates to the ordinary Cech cohomology object. -/
@[simp]
theorem pageTwoFunctor_obj (family : ι → Over U) (p q : ℕ)
    [HasProducts.{w} AddCommGrpCat.{z}]
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) :
    (pageTwoFunctor J U family p q).obj F =
      cechCohomology U family
        ((Sheaf.cohomologyPresheafFunctor.{z, v, u} J q).obj F) p := sorry

/-- The abutment target functor, namely site cohomology over the fixed object `U`. -/
@[stacks 03AZ "Cech spectral-sequence abutment target"]
abbrev abutmentFunctor (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{v})] (n : ℕ) :
    Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{z} :=
  Sheaf.cohomologyAtObjectFunctor.{z, v, u} J U n

/-- Evaluation of the second page of a coefficient-natural spectral-sequence functor at
bidegree `(p, q)`. -/
@[stacks 03AZ "second-page evaluation functor"]
abbrev pageTwoSource
    (E : Sheaf J AddCommGrpCat.{v} ⥤
      E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{z})
    (p q : ℕ) : Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{z} :=
  E ⋙
    SpectralSequence.pageFunctor AddCommGrpCat.{z} _ 2 (2 : ℤ) ⋙
      HomologicalComplex.eval AddCommGrpCat.{z} _ (p, q)

/-- A coefficient-natural first-quadrant spectral sequence for a Cech covering family, with its
canonical `E₂` page and site-cohomology abutment. -/
@[stacks 03AZ "Cech spectral-sequence system"]
structure SpectralSequenceSystem
    (J : GrothendieckTopology C) (U : C) (family : ι → Over U)
    [HasFiniteProducts (Over U)]
    [HasProducts.{w} AddCommGrpCat.{z}]
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{v})] where
  /-- The spectral sequence, functorial in the coefficient sheaf. -/
  functor :
    Sheaf J AddCommGrpCat.{v} ⥤
      E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{z}
  /-- The second page is naturally isomorphic to Cech cohomology of the cohomology presheaf. -/
  pageTwoComparison (p q : ℕ) :
    pageTwoSource functor p q ≅ pageTwoFunctor J U family p q
  /-- Each coefficient spectral sequence converges to site cohomology over `U`. -/
  converges :
    ∀ (F : Sheaf J AddCommGrpCat.{v}),
      E₂CohomologicalSpectralSequenceNat.ConvergesTo
        (functor.obj F)
        (fun n ↦ (abutmentFunctor J U n).obj F)

/-- A covering family admits a coefficient-natural Cech spectral-sequence system whose second page
is Cech cohomology of the cohomology presheaves and whose abutment is site cohomology over `U`. -/
@[stacks 03AZ "existence of a Cech spectral-sequence system"]
theorem spectralSequenceSystem_nonempty (family : ι → Over U)
    [HasProducts.{w} AddCommGrpCat.{z}]
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{v})]
    (hfamily : (J.over U).CoversTop family) :
    Nonempty (SpectralSequenceSystem J U family) := sorry

namespace SpectralSequenceSystem

variable {family : ι → Over U}
variable [HasProducts.{w} AddCommGrpCat.{z}]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{z} (Sheaf J AddCommGrpCat.{v})]

/-- A nonempty coefficient-natural Cech spectral-sequence system supplies a chosen system. -/
noncomputable def ofNonempty (h : Nonempty (SpectralSequenceSystem J U family)) :
    SpectralSequenceSystem J U family :=
  Classical.choice h

/-- The page-two identification for one bidegree and coefficient sheaf. -/
@[stacks 03AZ "second-page identification component"]
abbrev pageTwoIso (S : SpectralSequenceSystem J U family)
    (p q : ℕ) (F : Sheaf J AddCommGrpCat.{v}) :
    ((S.functor.obj F).page 2 le_rfl).X (p, q) ≅
      (pageTwoFunctor J U family p q).obj F :=
  (S.pageTwoComparison p q).app F

/-- Naturality of the second-page identification in the coefficient sheaf. -/
@[stacks 03AZ "second-page identification naturality", reassoc]
theorem pageTwo_naturality (S : SpectralSequenceSystem J U family)
    {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (p q : ℕ) :
    (((S.functor.map φ).hom 2 le_rfl).f (p, q)) ≫
        (S.pageTwoIso p q G).hom =
      (S.pageTwoIso p q F).hom ≫
        (pageTwoFunctor J U family p q).map φ := sorry

/-- Naturality of the inverse second-page identification in the coefficient sheaf. -/
@[stacks 03AZ "inverse second-page identification naturality", reassoc]
theorem pageTwo_naturality_inv (S : SpectralSequenceSystem J U family)
    {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (p q : ℕ) :
    (pageTwoFunctor J U family p q).map φ ≫
        (S.pageTwoIso p q G).inv =
      (S.pageTwoIso p q F).inv ≫
        ((S.functor.map φ).hom 2 le_rfl).f (p, q) := sorry

/-- The convergence assertion for one coefficient sheaf. -/
@[stacks 03AZ "Cech spectral-sequence convergence component"]
abbrev converges_app (S : SpectralSequenceSystem J U family)
    (F : Sheaf J AddCommGrpCat.{v}) :
    E₂CohomologicalSpectralSequenceNat.ConvergesTo
      (S.functor.obj F)
      (fun n ↦ (abutmentFunctor J U n).obj F) := S.converges F

/-- Convergence supplies the corresponding abutment for one coefficient sheaf. -/
@[stacks 03AZ "Cech spectral-sequence abutment component"]
theorem abuts_app (S : SpectralSequenceSystem J U family)
    (F : Sheaf J AddCommGrpCat.{v}) :
    E₂CohomologicalSpectralSequenceNat.AbutsTo
      (S.functor.obj F)
      (fun n ↦ (abutmentFunctor J U n).obj F) := sorry

end SpectralSequenceSystem

end CategoryTheory.Cech
