/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting a quasi-isomorphism along a surjection of ring sheaves

On a site, a quasi-isomorphism `K₀ ⟶ F ⊗_O O₀` along a locally surjective
map of ring sheaves `O ⟶ O₀` lifts to a quasi-isomorphism `G ⟶ F` whose
extension of scalars factors through `K₀` in the homotopy category of
`O₀`-module complexes.
-/

@[expose] public section

open CategoryTheory ComplexShape SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

/-- A morphism `f : K ⟶ M` of cochain complexes of `O₀`-modules factors through
`g : L ⟶ M` in the homotopy category if there exists `h : K ⟶ L` with
`(HomotopyCategory.quotient (ringedSiteModuleCategory J O₀) (up ℤ)).map f =
(HomotopyCategory.quotient (ringedSiteModuleCategory J O₀) (up ℤ)).map (h ≫ g)`. -/
def homotopyFactorsThru {O₀ : Sheaf J CommRingCat.{u}}
    {K L M : CochainComplex (ringedSiteModuleCategory J O₀) ℤ}
    (f : K ⟶ M) (g : L ⟶ M) : Prop :=
  ∃ (h : K ⟶ L),
    (HomotopyCategory.quotient (ringedSiteModuleCategory J O₀) (up ℤ)).map f =
      (HomotopyCategory.quotient (ringedSiteModuleCategory J O₀) (up ℤ)).map (h ≫ g)

/-- Factoring through `g` in the homotopy category is equivalent to the existence of a
homotopy between `f` and a composite `h ≫ g`. -/
theorem homotopyFactorsThru_iff {O₀ : Sheaf J CommRingCat.{u}}
    {K L M : CochainComplex (ringedSiteModuleCategory J O₀) ℤ}
    (f : K ⟶ M) (g : L ⟶ M) :
    homotopyFactorsThru f g ↔ ∃ h, Nonempty (Homotopy f (h ≫ g)) := sorry

variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Lemma 91.16.5: Let `C` be a site. Let `π : O ⟶ O₀` be a surjection of sheaves of rings.
Given a complex `F` of `O`-modules, a complex `K₀` of `O₀`-modules, and a quasi-isomorphism
`α : K₀ ⟶ (extendComplex π).obj F`, there exists a quasi-isomorphism `q : G ⟶ F` such that
`(extendComplex π).map q` factors through `α` in the homotopy category of complexes of
`O₀`-modules. -/
@[stacks 0DIX]
theorem exists_quasiIso_homotopyFactor
    {O O₀ : Sheaf J CommRingCat.{u}} (π : O ⟶ O₀)
    [Sheaf.IsLocallySurjective π]
    (F : CochainComplex (ringedSiteModuleCategory J O) ℤ)
    (K₀ : CochainComplex (ringedSiteModuleCategory J O₀) ℤ)
    (α : K₀ ⟶ (extendComplex π).obj F) [QuasiIso α] :
    ∃ (G : CochainComplex (ringedSiteModuleCategory J O) ℤ) (q : G ⟶ F),
      QuasiIso q ∧ homotopyFactorsThru ((extendComplex π).map q) α := sorry

end SheafOfModules.RingedSite
