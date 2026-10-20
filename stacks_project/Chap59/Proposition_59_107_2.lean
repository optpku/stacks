/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Proposition 59.107.2: if `p` is prime and `S` is a quasi-compact and
quasi-separated scheme of characteristic `p`, then
`H^i((Sch/S)_h, 𝒪^h)` identifies with `colim_F H^i(S, 𝒪)`, where `𝒪^h` is
the h-sheafification of the structure sheaf. -/
@[stacks 0EWU] #check
  (AlgebraicGeometry.Scheme.H.hCohomology_structureSheaf_iso_frobeniusColimit :
    ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
      [CompactSpace S] [QuasiSeparatedSpace S] (i : ℕ)
      [HasSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}]
      [HasSheafify ((Scheme.hPrecoverage.toGrothendieck).over S)
        AddCommGrpCat.{u + 1}]
      [HasExt (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})]
      [HasExt (Sheaf ((Scheme.hPrecoverage.toGrothendieck).over S)
          AddCommGrpCat.{u + 1})]
      [HasColimit
        (AlgebraicGeometry.Scheme.H.structureSheafCohomologyFrobeniusIterate
          p S i)],
    IsIso
      (AlgebraicGeometry.Scheme.H.hCohomologyComparison p S i))

end

end
