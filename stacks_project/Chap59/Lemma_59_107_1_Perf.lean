module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.PerfectStructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

/- The perfect structure sheaf remains available through its shared mathematical owner. -/
#check (AlgebraicGeometry.Scheme.perfStructureSheaf :
    ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
      [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}],
      Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})

end

end
