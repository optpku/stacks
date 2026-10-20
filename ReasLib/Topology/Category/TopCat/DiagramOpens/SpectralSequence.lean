module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Cohomology
public import ReasLib.CategoryTheory.Homology.SpectralSequence.FiniteAbutment

/-!
# The cohomological spectral sequence of a simplicial topological space

Component cohomology forms the first page of a coefficient-functorial spectral
sequence with finite abutment to cohomology on the diagram-open Zariski site.
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

/-- Abelian sheaves on a simplicial topological space have a functorial
first-quadrant spectral sequence starting at page zero, with natural first-page
identifications with component cohomology and finite abutment to Zariski cohomology. -/
theorem zariskiSpectralSequence_functorial :
    ∃ (E : Sheaf (zariskiTopology X) AddCommGrpCat.{u} ⥤
        CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 0)
      (pageOneIso :
        ∀ (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u}) (p q : ℕ),
          ((E.obj F).page 1 (by decide)).X (p, q) ≅ componentCohomology X F p q),
      (∀ F, CohomologicalSpectralSequenceNat.FinitelyAbutsTo (E.obj F)
          (zariskiCohomology X F)) ∧
        ∀ {F G : Sheaf (zariskiTopology X) AddCommGrpCat.{u}} (α : F ⟶ G) (p q : ℕ),
          (pageOneIso F p q).hom ≫ (componentCohomologyFunctor X p q).map α =
            ((E.map α).hom 1 (by decide)).f (p, q) ≫ (pageOneIso G p q).hom :=
  sorry

/-- Every abelian sheaf on a simplicial topological space admits a first-quadrant
spectral sequence starting at page zero, whose first page is component cohomology
and which finitely abuts to Zariski cohomology. -/
theorem exists_zariskiSpectralSequence
    (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u}) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 0)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 (by decide)).X (p, q) ≅ componentCohomology X F p q),
      CohomologicalSpectralSequenceNat.FinitelyAbutsTo E (zariskiCohomology X F) := by
  obtain ⟨E, pageOneIso, hAbuts, _⟩ := zariskiSpectralSequence_functorial X
  exact ⟨E.obj F, pageOneIso F, hAbuts F⟩

end CategoryTheory.SimplicialObject
