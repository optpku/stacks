module

public import ReasLib.CategoryTheory.Sites.Cech.SpectralSequence.Terminal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presheaf.Cech

noncomputable section

universe z w v u

/- 96.23.3.2 After `g⁻¹ h_x ⟶ ∗` is surjective on `X'_τ`, the Čech-to-cohomology
spectral sequence of Cohomology on Sites 079Z gives
`E₁^{p, q} = H^q(g⁻¹ h_{x,p}, g⁻¹ F) ⇒ H^{p+q}(X'_τ, g⁻¹ F)`, where `h_{x,p}` is
the `(p+1)`-fold product of the representable sheaf `h_x`. Instantiating with
site `J = X'_τ`, `K'` the underlying presheaf of `g⁻¹ h_x`, and coefficient sheaf
`F` in the role of `g⁻¹ F`, the first page is cohomology over the sheafified Čech
levels of the unique map `K' ⟶ ∗` and the abutment is global sheaf cohomology.
Exact inverse image preserves finite products, so the degree-`p` levels represent
`g⁻¹ h_{x,p}`, the `(p+1)`-fold products of `g⁻¹ h_x`. -/
@[stacks 07AM] #check
  (CategoryTheory.Presheaf.Cech.exists_spectralSequence_terminal :
    ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type (max w v))]
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    {K' : Cᵒᵖ ⥤ Type (max w v)}
    [Presheaf.IsLocallySurjective J ((Presheaf.terminalIsTerminal C).from K')]
    (F : Sheaf J AddCommGrpCat.{max w v}),
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{z} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          (pageOneFunctor ((Presheaf.terminalIsTerminal C).from K') p q).obj F),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH.{z, max w v, v, u} J n).obj F))
