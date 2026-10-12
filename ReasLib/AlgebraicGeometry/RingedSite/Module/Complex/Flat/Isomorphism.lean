/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.Isomorphism
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Flat

/-!
# Isomorphism transport for termwise-flat complexes

The canonical transport API is `HomologicalComplex.IsTermwiseFlat.of_iso` and
`HomologicalComplex.IsTermwiseFlat.iff_of_iso`.  This leaf retains ringed-site specializations for
compatibility with source-facing statements.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.CochainComplex

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Termwise flatness is invariant under an isomorphism of cochain complexes. -/
theorem isTermwiseFlat_of_iso
    {K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ} (e : K ≅ L)
    (hK : IsTermwiseFlat K) : IsTermwiseFlat L := sorry

/-- The reverse transport of termwise flatness along a complex isomorphism. -/
theorem isTermwiseFlat_of_iso_symm
    {K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ} (e : K ≅ L)
    (hL : IsTermwiseFlat L) : IsTermwiseFlat K := sorry

end

end SheafOfModules.RingedSite.CochainComplex
