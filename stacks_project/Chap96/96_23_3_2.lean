/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.SpectralSequence.Presheaf
public import ReasLib.CategoryTheory.Sites.Cohomology.Terminal
import Mathlib.Tactic.CrossRefAttribute

/-!
# 96.23.3.2

The Čech-to-cohomology spectral sequence of a locally surjective map `K' ⟶ ∗` of
type-valued presheaves, specialized from Cohomology on Sites 079Z so that the
abutment is cohomology of the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presheaf.Cech

noncomputable section

universe z w v u

namespace CategoryTheory.Presheaf.Cech

variable {C : Type u} [Category.{v} C]

/-- 96.23.3.2 After `g⁻¹ h_x ⟶ ∗` is surjective on `X'_τ`, the Čech-to-cohomology
spectral sequence of Cohomology on Sites 079Z gives
`E₁^{p, q} = H^q(g⁻¹ h_{x,p}, g⁻¹ F) ⇒ H^{p+q}(X'_τ, g⁻¹ F)`, where `h_{x,p}` is
the `(p+1)`-fold product of the representable sheaf `h_x`. Instantiating with
site `J = X'_τ`, `K'` the underlying presheaf of `g⁻¹ h_x`, and coefficient sheaf
`F` in the role of `g⁻¹ F`, the first page is cohomology over the sheafified Čech
levels of the unique map `K' ⟶ ∗` and the abutment is cohomology over the
terminal presheaf. -/
@[stacks 07AM]
theorem exists_spectralSequence_terminal
    (J : GrothendieckTopology C)
    [HasSheafify J (Type (max w v))]
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    {K' : Cᵒᵖ ⥤ Type (max w v)}
    [Presheaf.IsLocallySurjective J ((Presheaf.terminalIsTerminal C).from K')]
    (F : Sheaf J AddCommGrpCat.{max w v}) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{z} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          (pageOneFunctor ((Presheaf.terminalIsTerminal C).from K') p q).obj F),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (abutmentFunctor (Presheaf.terminal C) n).obj F) := sorry

/-- The abutment of the Čech spectral sequence of `K' ⟶ ∗` is isomorphic to
ordinary sheaf cohomology `H^n(J, F)`. -/
theorem exists_spectralSequence_terminal.abutment_isomorphicGlobal
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    (F : Sheaf J AddCommGrpCat.{max w v}) (n : ℕ) :
    IsIsomorphic
      ((abutmentFunctor (Presheaf.terminal C) n).obj F)
      ((Sheaf.functorH J n).obj F) := sorry

end CategoryTheory.Presheaf.Cech
