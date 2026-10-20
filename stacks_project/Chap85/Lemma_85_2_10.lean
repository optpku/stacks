/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.SpectralSequence
import StacksCheckRecall

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

/- Lemma 85.2.10: component cohomology is the first page of a spectral sequence
starting at page zero and converging to Zariski cohomology, functorially in the
abelian coefficient sheaf. -/
@[stacks 09W6] #check (CategoryTheory.SimplicialObject.zariskiSpectralSequence_functorial X :
    ∃ (E : Sheaf (zariskiTopology X) AddCommGrpCat.{u} ⥤
        CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 0)
      (pageOneIso :
        ∀ (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u}) (p q : ℕ),
          ((E.obj F).page 1 (by decide)).X (p, q) ≅ componentCohomology X F p q),
      (∀ F, CohomologicalSpectralSequenceNat.FinitelyAbutsTo (E.obj F)
          (zariskiCohomology X F)) ∧
        ∀ {F G : Sheaf (zariskiTopology X) AddCommGrpCat.{u}} (α : F ⟶ G) (p q : ℕ),
          (pageOneIso F p q).hom ≫ (componentCohomologyFunctor X p q).map α =
            ((E.map α).hom 1 (by decide)).f (p, q) ≫ (pageOneIso G p q).hom)

#check (CategoryTheory.SimplicialObject.exists_zariskiSpectralSequence X :
    ∀ (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u}),
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 0)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 (by decide)).X (p, q) ≅ componentCohomology X F p q),
      CohomologicalSpectralSequenceNat.FinitelyAbutsTo E (zariskiCohomology X F))

end CategoryTheory.SimplicialObject
