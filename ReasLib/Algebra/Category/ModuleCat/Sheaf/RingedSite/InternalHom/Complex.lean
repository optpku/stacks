/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal Hom of complexes on a ringed site

This leaf specializes the generic internal-Hom map to complexes of module sheaves on a ringed
site and records its quasi-isomorphism behavior for K-injective targets.  The underlying map is
owned by `CategoryTheory.MonoidalClosed.Source.map`; only the sheaf-local homological statement
belongs here.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.IHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)]

/-- Lemma 21.34.7 (0A95): an internal-Hom map induced by quasi-isomorphisms is a
quasi-isomorphism when both target complexes are K-injective. -/
@[stacks 0A95 "quasi-isomorphism of internal-Hom complexes"]
theorem quasiIso_map
    {L' L I' I : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    [CochainComplex.IsKInjective I'] [CochainComplex.IsKInjective I]
    (f : L' ⟶ L) (g : I' ⟶ I) (h_f : QuasiIso f) (h_g : QuasiIso g) :
    QuasiIso (CategoryTheory.MonoidalClosed.Source.map f g) := sorry

/- The K-flat/K-injective consequence is a ringed-site internal-Hom fact.  It is deliberately a
theorem rather than an unconditional instance: `hL` is a mathematical input and cannot be
recovered by typeclass search from the complex alone. -/
/- The tensor structure needed to formulate K-flatness lives on the underlying module-sheaf
category, independently of the closed structure on its cochain complexes. -/
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

/-- A K-flat source and a K-injective target have K-injective internal Hom. -/
@[stacks 0A96 "K-injectivity of internal-Hom complexes"]
theorem isKInjective_of_isKFlat
    {L I : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (hL : L.IsKFlat) [I.IsKInjective] :
    ((CategoryTheory.ihom L).obj I).IsKInjective := sorry

end SheafOfModules.RingedSite.IHom

end
