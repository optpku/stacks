module

import StacksCheckRecall
public import ReasLib.Topology.Category.LCCat.ProperHypercovering.SpectralSequence

/-!
# Lemma 85.25.6

A first-quadrant spectral sequence with `E₁^{p,q} = H^q(U_p, F_p)` converging
to `H^{p+q}(X, F)`, for a proper hypercovering in `LCCat`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.SimplicialObject
open scoped Simplicial

noncomputable section

universe u v

/- Lemma 85.25.6. A proper hypercovering has a canonical spectral sequence
with first page `H^q(U_p, F_p)` converging to `H^{p+q}(X, F)`. -/
@[stacks 09XB] #check (LCCat.spectralSequence_functorial :
  ∀ {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})]
    [∀ n : ℕ, HasSheafify
      (Opens.grothendieckTopology ((LCCat.forgetToTop.obj U).obj (op ⦋n⦌))) AddCommGrpCat.{u}]
    [∀ n : ℕ, HasExt.{v}
      (Sheaf (Opens.grothendieckTopology ((LCCat.forgetToTop.obj U).obj (op ⦋n⦌)))
        AddCommGrpCat.{u})],
    LCCat.IsProperHypercovering a →
    ∃ (E : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u} ⥤
        CohomologicalSpectralSequenceNat AddCommGrpCat.{v} 1)
      (pageOneIso :
        ∀ (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}) (p q : ℕ),
          ((E.obj F).page 1 le_rfl).X (p, q) ≅
            stageCohomology (LCCat.toTopCatAugmentation a) F p q),
      (∀ F, CohomologicalSpectralSequenceNat.FinitelyAbutsTo (E.obj F)
          (fun n ↦ (Sheaf.functorH (Opens.grothendieckTopology X.obj) n).obj F)) ∧
        ∀ {F G : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}}
          (α : F ⟶ G) (p q : ℕ),
          (pageOneIso F p q).hom ≫
              (Sheaf.functorH
                (Opens.grothendieckTopology ((LCCat.forgetToTop.obj U).obj (op ⦋p⦌))) q).map
                ((stageInverseImage (LCCat.toTopCatAugmentation a) p).map α) =
            ((E.map α).hom 1 le_rfl).f (p, q) ≫ (pageOneIso G p q).hom)
