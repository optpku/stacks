/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import stacks_project.Chap85.Lemma_85_2_10_Cohomology

/-!
# Lemma 85.2.10

A first-quadrant spectral sequence with `E₁^{p,q} = H^q(X_p, F_p)` converging
to `H^{p+q}(X_Zar, F)`, functorial in the abelian sheaf `F`.
-/

@[expose] public section

open CategoryTheory Opposite TopCat
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable (X : SimplicialObject TopCat.{u})
variable [HasSheafify (zariskiTopology X) AddCommGrpCat.{u}]
variable [HasExt.{v} (Sheaf (zariskiTopology X) AddCommGrpCat.{u})]
variable [∀ n : ℕ, HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) AddCommGrpCat.{u}]
variable [∀ n : ℕ, HasExt.{v} (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) AddCommGrpCat.{u})]

/-- Lemma 85.2.10 (1): for a simplicial topological space `X` and an abelian sheaf `F`
on `X_Zar`, there is a first-quadrant spectral sequence with
`E₁^{p,q} = H^q(X_p, F_p)` converging to `H^{p+q}(X_Zar, F)`. -/
@[stacks 09W6]
theorem exists_zariskiSpectralSequence
    (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u}) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ componentCohomology X F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E (zariskiCohomology X F) :=
  sorry

/-- Lemma 85.2.10 (2): the Zariski spectral sequence of a simplicial topological
space is functorial in the abelian sheaf `F`. -/
@[stacks 09W6]
theorem zariskiSpectralSequence_functorial :
    ∃ (E : Sheaf (zariskiTopology X) AddCommGrpCat.{u} ⥤
        CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 1)
      (pageOneIso :
        ∀ (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u}) (p q : ℕ),
          ((E.obj F).page 1 le_rfl).X (p, q) ≅ componentCohomology X F p q),
      (∀ F, CohomologicalSpectralSequenceNat.ConvergesTo (E.obj F)
          (zariskiCohomology X F)) ∧
        ∀ {F G : Sheaf (zariskiTopology X) AddCommGrpCat.{u}} (α : F ⟶ G) (p q : ℕ),
          (pageOneIso F p q).hom ≫ (componentCohomologyFunctor X p q).map α =
            ((E.map α).hom 1 le_rfl).f (p, q) ≫ (pageOneIso G p q).hom :=
  sorry

end CategoryTheory.SimplicialObject
