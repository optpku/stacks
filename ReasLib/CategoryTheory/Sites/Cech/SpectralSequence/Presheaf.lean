/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech spectral sequences for locally surjective presheaf maps

A locally surjective map of type-valued presheaves determines a first-quadrant spectral sequence.
Its first page is cohomology over the sheafified Cech nerve, and it converges to cohomology over
the target presheaf.  The primary owner is natural in the abelian coefficient sheaf.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe z w v u

namespace CategoryTheory.Presheaf.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J (Type (max w v))]
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]

/-- The Cech nerve of a presheaf map after applying set-valued sheafification. -/
@[stacks 079Z "sheafified Cech nerve"]
abbrev sheafifiedNerve
    {K K' : Cᵒᵖ ⥤ Type (max w v)} (φ : K' ⟶ K) :
    SimplicialObject (Sheaf J (Type (max w v))) :=
  (Arrow.mk ((presheafToSheaf J (Type (max w v))).map φ)).cechNerve

/-- The degree-`p` object of the sheafified Cech nerve of a presheaf map. -/
@[stacks 079Z "sheafified Cech level"]
abbrev sheafifiedLevel
    {K K' : Cᵒᵖ ⥤ Type (max w v)} (φ : K' ⟶ K) (p : ℕ) :
    Sheaf J (Type (max w v)) :=
  (sheafifiedNerve φ).obj (op (SimplexCategory.mk p))

/-- The first-page target in bidegree `(p, q)`, functorial in the coefficient sheaf. -/
@[stacks 079Z "Cech spectral-sequence first-page target"]
abbrev pageOneFunctor
    {K K' : Cᵒᵖ ⥤ Type (max w v)} (φ : K' ⟶ K) (p q : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{z} :=
  Sheaf.cohomologyOverSheafFunctor (sheafifiedLevel φ p) q

/-- The abutment target, namely cohomology over the target presheaf. -/
@[stacks 079Z "Cech spectral-sequence abutment target"]
abbrev abutmentFunctor
    (K : Cᵒᵖ ⥤ Type (max w v)) (n : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{z} :=
  Sheaf.cohomologyOverPresheafFunctor J K n

/-- Evaluation of a coefficient-natural spectral-sequence functor on its first page at
bidegree `(p, q)`. -/
@[stacks 079Z "Cech spectral-sequence first-page source"]
abbrev pageOneSource
    (E : Sheaf J AddCommGrpCat.{max w v} ⥤
      CohomologicalSpectralSequenceNat AddCommGrpCat.{z} 1)
    (p q : ℕ) : Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{z} :=
  E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{z} _ 1 (1 : ℤ) ⋙
    HomologicalComplex.eval AddCommGrpCat.{z} _ (p, q)

/-- A coefficient-natural first-quadrant Cech spectral sequence attached to a presheaf map. -/
@[stacks 079Z "Cech spectral-sequence system"]
structure SpectralSequenceSystem
    {K K' : Cᵒᵖ ⥤ Type (max w v)} (φ : K' ⟶ K) where
  /-- The first-quadrant spectral sequence, functorial in the coefficient sheaf. -/
  functor :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      CohomologicalSpectralSequenceNat AddCommGrpCat.{z} 1
  /-- Its first page is naturally the cohomology of the sheafified Cech levels. -/
  pageOneComparison (p q : ℕ) :
    pageOneSource functor p q ≅ pageOneFunctor φ p q
  /-- It converges to cohomology over the target presheaf. -/
  converges (F : Sheaf J AddCommGrpCat.{max w v}) :
    CohomologicalSpectralSequenceNat.ConvergesTo
      (functor.obj F) (fun n ↦ (abutmentFunctor K n).obj F)

/-- A locally surjective presheaf map admits a coefficient-natural Cech spectral-sequence
system. -/
@[stacks 079Z "existence of a Cech spectral-sequence system"]
theorem spectralSequenceSystem_nonempty
    {K K' : Cᵒᵖ ⥤ Type (max w v)} (φ : K' ⟶ K)
    [Presheaf.IsLocallySurjective J φ] :
    Nonempty (SpectralSequenceSystem.{z, w, v, u} (J := J) φ) := sorry

namespace SpectralSequenceSystem

variable {K K' : Cᵒᵖ ⥤ Type (max w v)} {φ : K' ⟶ K}

/-- The first-page identification for one bidegree and coefficient sheaf. -/
@[stacks 079Z "Cech first-page identification component"]
abbrev pageOneIso (S : SpectralSequenceSystem φ)
    (p q : ℕ) (F : Sheaf J AddCommGrpCat.{max w v}) :
    ((S.functor.obj F).page 1 le_rfl).X (p, q) ≅
      (pageOneFunctor φ p q).obj F :=
  (S.pageOneComparison p q).app F

/-- Naturality of the first-page identification in the coefficient sheaf. -/
@[stacks 079Z "Cech first-page identification naturality", reassoc]
theorem pageOne_naturality (S : SpectralSequenceSystem φ)
    {F G : Sheaf J AddCommGrpCat.{max w v}} (f : F ⟶ G) (p q : ℕ) :
    (((S.functor.map f).hom 1 le_rfl).f (p, q)) ≫
        (S.pageOneIso p q G).hom =
      (S.pageOneIso p q F).hom ≫ (pageOneFunctor φ p q).map f := sorry

/-- The convergence assertion for one coefficient sheaf. -/
@[stacks 079Z "Cech spectral-sequence convergence component"]
abbrev converges_app (S : SpectralSequenceSystem φ)
    (F : Sheaf J AddCommGrpCat.{max w v}) :
    CohomologicalSpectralSequenceNat.ConvergesTo
      (S.functor.obj F) (fun n ↦ (abutmentFunctor K n).obj F) :=
  S.converges F

/-- The corresponding abutment for one coefficient sheaf. -/
@[stacks 079Z "Cech spectral-sequence abutment component"]
theorem abuts_app (S : SpectralSequenceSystem φ)
    (F : Sheaf J AddCommGrpCat.{max w v}) :
    CohomologicalSpectralSequenceNat.AbutsTo
      (S.functor.obj F) (fun n ↦ (abutmentFunctor K n).obj F) := sorry

end SpectralSequenceSystem

/-- Lemma 21.13.2 (079Z): a locally surjective presheaf map admits a first-quadrant spectral
sequence with `E₁^{p,q}` equal to cohomology over its sheafified degree-`p` Cech level and
abutment equal to cohomology over its target. -/
@[stacks 079Z]
theorem exists_spectralSequence
    {K K' : Cᵒᵖ ⥤ Type (max w v)} (φ : K' ⟶ K)
    [Presheaf.IsLocallySurjective J φ]
    (F : Sheaf J AddCommGrpCat.{max w v}) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{z} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ (pageOneFunctor φ p q).obj F),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (abutmentFunctor K n).obj F) := sorry

end CategoryTheory.Presheaf.Cech
