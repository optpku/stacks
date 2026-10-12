/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

/-- The étale topology on schemes is coarser than the fpqc topology. -/
theorem etaleTopology_le_fpqcTopology :
    etaleTopology ≤ fpqcTopology := sorry

/-- The big smooth topology on schemes is coarser than the fpqc topology. -/
theorem bigSmoothSite_le_fpqcTopology :
    bigSmoothSite ≤ fpqcTopology := sorry

/-- The big syntomic topology on schemes is coarser than the fpqc topology. -/
theorem bigSyntomicSite_le_fpqcTopology :
    bigSyntomicSite ≤ fpqcTopology := sorry

/-- An fpqc sheaf on schemes over a fixed scheme is a sheaf for any topology
coarser than the fpqc topology. -/
theorem isSheaf_of_fpqc_of_le
    (S : Scheme.{u}) {J : GrothendieckTopology Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type v)
    (hJ : J ≤ fpqcTopology)
    (hF : Presieve.IsSheaf (fpqcTopology.over S) F) :
    Presieve.IsSheaf (J.over S) F := sorry

/-- Every representable presheaf on schemes over a fixed scheme is a sheaf
for the étale topology. -/
theorem isSheaf_etale_of_isRepresentable
    (S : Scheme.{u}) (P : (Over S)ᵒᵖ ⥤ Type v) [P.IsRepresentable] :
    Presieve.IsSheaf (etaleTopology.over S) P := sorry

end AlgebraicGeometry.Scheme
