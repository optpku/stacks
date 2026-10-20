module

public import ReasLib.Topology.Sheaves.Simplicial.StageCohomology
public import ReasLib.Topology.Category.LCCat.Simplicial
public import ReasLib.Topology.Category.LCCat.ProperHypercovering
public import ReasLib.CategoryTheory.Homology.SpectralSequence.FiniteAbutment

/-!
# The cohomological spectral sequence of a proper hypercovering

Degreewise pullback cohomology forms the first page of a coefficient-functorial
spectral sequence finitely abutting to cohomology of the augmented space.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.SimplicialObject
open scoped Simplicial

noncomputable section

universe u v

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
variable [HasExt.{v} (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})]
variable [∀ n : ℕ, HasSheafify
    (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋n⦌))) AddCommGrpCat.{u}]
variable [∀ n : ℕ, HasExt.{v}
    (Sheaf (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋n⦌))) AddCommGrpCat.{u})]

/-- A proper hypercovering of a Hausdorff locally compact space has a
coefficient-functorial first-quadrant spectral sequence starting at page one,
with natural first-page identifications with degreewise pullback cohomology
and finite abutment to cohomology of the augmented space. -/
theorem spectralSequence_functorial (ha : IsProperHypercovering a) :
    ∃ (E : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u} ⥤
        CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 1)
      (pageOneIso :
        ∀ (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}) (p q : ℕ),
          ((E.obj F).page 1 le_rfl).X (p, q) ≅
            stageCohomology (toTopCatAugmentation a) F p q),
      (∀ F, CohomologicalSpectralSequenceNat.FinitelyAbutsTo (E.obj F)
          (fun n ↦ (Sheaf.functorH (Opens.grothendieckTopology X.obj) n).obj F)) ∧
        ∀ {F G : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}}
          (α : F ⟶ G) (p q : ℕ),
          (pageOneIso F p q).hom ≫
              (Sheaf.functorH
                (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op ⦋p⦌))) q).map
                ((stageInverseImage (toTopCatAugmentation a) p).map α) =
            ((E.map α).hom 1 le_rfl).f (p, q) ≫ (pageOneIso G p q).hom :=
  sorry

end LCCat
