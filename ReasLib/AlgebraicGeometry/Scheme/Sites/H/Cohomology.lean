module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.PerfectStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.PerfectStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.CategoryTheory.Sites.Sheafification.Map

/-!
# H-sheaf cohomology of the structure sheaf

This module defines the h-sheafification of the structure presheaf, the
Frobenius cohomology diagram, and its comparison with h-site cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.H

/-- The additive structure presheaf on `(Over S)ᵒᵖ`, valued in abelian groups. -/
def additiveHStructurePresheaf (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Scheme.Over.commStructurePresheaf (Functor.id (Over S)) ⋙ commRingToAddCommGrp

/-- The h-sheafification `𝒪^h` of the additive structure presheaf on `(Sch/S)_h`. -/
def hStructureSheaf (S : Scheme.{u})
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S) AddCommGrpCat.{u + 1}] :
    Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}).obj
    (additiveHStructurePresheaf S)

/-- The sheafification unit from the additive structure presheaf to `𝒪^h`. -/
def hStructureSheafToPresheaf (S : Scheme.{u})
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S) AddCommGrpCat.{u + 1}] :
    additiveHStructurePresheaf S ⟶ (hStructureSheaf S).obj :=
  (sheafificationAdjunction ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}).unit.app
    (additiveHStructurePresheaf S)

/-- The h-sheafification unit satisfies the sheafification universal property. -/
theorem hStructureSheaf_isSheafification (S : Scheme.{u})
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S) AddCommGrpCat.{u + 1}] :
    Presheaf.IsSheafification ((Scheme.hPrecoverage.toGrothendieck).over S)
      (hStructureSheafToPresheaf S) :=
  sorry

/-- Degree-`i` fppf cohomology of the additive structure sheaf. -/
def structureSheafCohomology (S : Scheme.{u}) (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})] :
    AddCommGrpCat.{u + 1} :=
  (Sheaf.functorH (Scheme.fppfTopology.over S) i).obj (additiveBigFppfStructureSheaf S)

/-- The endomorphism of structure-sheaf cohomology induced by Frobenius. -/
def structureSheafCohomologyFrobenius
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})] :
    structureSheafCohomology S i ⟶ structureSheafCohomology S i :=
  (Sheaf.functorH (Scheme.fppfTopology.over S) i).map (structureSheafFrobenius p S)

/-- The sequential diagram of structure-sheaf cohomology under Frobenius. -/
def structureSheafCohomologyFrobeniusIterate
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})] :
    ℕ ⥤ AddCommGrpCat.{u + 1} :=
  Functor.ofSequence (fun _ : ℕ ↦ structureSheafCohomologyFrobenius p S i)

/-- Every object of the Frobenius cohomology diagram is structure-sheaf cohomology. -/
theorem structureSheafCohomologyFrobeniusIterate_obj
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})] (n : ℕ) :
    (structureSheafCohomologyFrobeniusIterate p S i).obj n =
      structureSheafCohomology S i :=
  sorry

/-- Every successor arrow of the Frobenius cohomology diagram is Frobenius. -/
theorem structureSheafCohomologyFrobeniusIterate_map_succ
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})] (n : ℕ) :
    (structureSheafCohomologyFrobeniusIterate p S i).map (homOfLE n.le_succ) =
      structureSheafCohomologyFrobenius p S i :=
  sorry

/-- The sequential colimit of Frobenius structure-sheaf cohomology. -/
def structureSheafCohomologyFrobeniusColimit
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})]
    [HasColimit (structureSheafCohomologyFrobeniusIterate p S i)] :
    AddCommGrpCat.{u + 1} :=
  colimit (structureSheafCohomologyFrobeniusIterate p S i)

/-- The h-sheafification of the additive fppf structure presheaf. -/
def structureSheafAsHSheaf (S : Scheme.{u})
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}] :
    Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}).obj
    (additiveBigFppfStructureSheaf S).obj

/-- The sheafification map from the fppf structure presheaf to the h-sheaf model. -/
def structureSheafToHStructure (S : Scheme.{u})
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}] :
    structureSheafAsHSheaf S ⟶ hStructureSheaf S :=
  (presheafToSheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}).map
    (𝟙 (additiveHStructurePresheaf S) :
      (additiveBigFppfStructureSheaf S).obj ⟶ additiveHStructurePresheaf S)

/-- The h-sheaf `𝒪^h` viewed as a sheaf on the fppf site. -/
def hStructureSheafAsFppf (S : Scheme.{u})
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}] :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} where
  obj := (hStructureSheaf S).obj
  property := sorry

/-- The fppf-sheaf map from the structure sheaf to the h-sheaf `𝒪^h`. -/
def structureSheafToHStructureFppf (S : Scheme.{u})
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}] :
    additiveBigFppfStructureSheaf S ⟶ hStructureSheafAsFppf S where
  hom := hStructureSheafToPresheaf S

/-- Fppf cohomology of the h-sheaf model agrees with its h-site cohomology. -/
theorem hCohomology_fppfView_eq_asH (S : Scheme.{u}) (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
        AddCommGrpCat.{u + 1})] :
    (Sheaf.functorH (Scheme.fppfTopology.over S) i).obj (hStructureSheafAsFppf S) =
      (Sheaf.functorH ((Scheme.hPrecoverage.toGrothendieck).over S) i).obj
        (structureSheafAsHSheaf S) :=
  sorry

/-- The stage map from fppf structure-sheaf cohomology to h-site cohomology. -/
def structureSheafCohomologyToHStage (S : Scheme.{u}) (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
        AddCommGrpCat.{u + 1})] :
    structureSheafCohomology S i ⟶
      (Sheaf.functorH ((Scheme.hPrecoverage.toGrothendieck).over S) i).obj
        (structureSheafAsHSheaf S) :=
  (Sheaf.functorH (Scheme.fppfTopology.over S) i).map
      (structureSheafToHStructureFppf S) ≫
    eqToHom (hCohomology_fppfView_eq_asH S i)

/-- The stage map from structure-sheaf cohomology into `H^i((Sch/S)_h, 𝒪^h)`. -/
def hCohomologyStage (S : Scheme.{u}) (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
        AddCommGrpCat.{u + 1})] :
    structureSheafCohomology S i ⟶
      (Sheaf.functorH ((Scheme.hPrecoverage.toGrothendieck).over S) i).obj
        (hStructureSheaf S) :=
  structureSheafCohomologyToHStage S i ≫
    (Sheaf.functorH ((Scheme.hPrecoverage.toGrothendieck).over S) i).map
      (structureSheafToHStructure S)

/-- The Frobenius-stage cocone with vertex h-site cohomology of `𝒪^h`. -/
def hCohomologyComparisonCocone
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
        AddCommGrpCat.{u + 1})] :
    Cocone (structureSheafCohomologyFrobeniusIterate p S i) where
  pt := (Sheaf.functorH ((Scheme.hPrecoverage.toGrothendieck).over S) i).obj
    (hStructureSheaf S)
  ι :=
    { app := fun _ ↦ hCohomologyStage S i
      naturality := fun _ _ _ ↦ sorry }

/-- The canonical comparison from the Frobenius colimit to h-site cohomology. -/
def hCohomologyComparison
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
        AddCommGrpCat.{u + 1})]
    [HasColimit (structureSheafCohomologyFrobeniusIterate p S i)] :
    structureSheafCohomologyFrobeniusColimit p S i ⟶
      (Sheaf.functorH ((Scheme.hPrecoverage.toGrothendieck).over S) i).obj
        (hStructureSheaf S) :=
  colimit.desc (structureSheafCohomologyFrobeniusIterate p S i)
    (hCohomologyComparisonCocone p S i)

/-- The comparison restricts on each colimit stage to the corresponding stage map. -/
theorem hCohomologyComparison_ι
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
        AddCommGrpCat.{u + 1})]
    [HasColimit (structureSheafCohomologyFrobeniusIterate p S i)] (n : ℕ) :
    colimit.ι (structureSheafCohomologyFrobeniusIterate p S i) n ≫
        hCohomologyComparison p S i =
      hCohomologyStage S i :=
  sorry

/-- For a quasi-compact, quasi-separated characteristic-`p` scheme, the
Frobenius-colimit comparison with h-site cohomology is an isomorphism. -/
theorem hCohomology_structureSheaf_iso_frobeniusColimit
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    [CompactSpace S] [QuasiSeparatedSpace S] (i : ℕ)
    [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
      AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
        AddCommGrpCat.{u + 1})]
    [HasColimit (structureSheafCohomologyFrobeniusIterate p S i)] :
    IsIso (hCohomologyComparison p S i) :=
  sorry

end AlgebraicGeometry.Scheme.H

end

end
