module

public import ReasLib.CategoryTheory.Sites.Cech.SpectralSequence.Presheaf
public import ReasLib.CategoryTheory.Sites.Cohomology.Terminal

/-!
# Terminal Čech spectral sequences

A locally surjective map to the terminal presheaf determines a first-quadrant Čech
spectral sequence converging to global sheaf cohomology.
-/

@[expose] public section

noncomputable section

universe z w v u

namespace CategoryTheory.Presheaf.Cech

variable {C : Type u} [Category.{v} C]

/-- A locally surjective map to the terminal presheaf admits a first-quadrant Čech
spectral sequence whose first page is cohomology over the sheafified Čech levels
and whose abutment is global sheaf cohomology. -/
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
        (fun n ↦ (Sheaf.functorH.{z, max w v, v, u} J n).obj F) := sorry

/-- A representable presheaf whose map to the terminal presheaf is locally surjective gives
a first-quadrant spectral sequence for every abelian coefficient sheaf. Its first page is
cohomology over finite powers of the sheafified representable, and it converges to global
sheaf cohomology. -/
theorem exists_spectralSequence_yoneda
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type (max w v))]
    [HasSheafify J AddCommGrpCat.{max w v}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
    (x : C)
    [Presheaf.IsLocallySurjective J
      ((Presheaf.terminalIsTerminal.{max w v} C).from (uliftYoneda.{w}.obj x))]
    (F : Sheaf J AddCommGrpCat.{max w v}) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{z} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          (Sheaf.cohomologyOverSheafFunctor
            (Limits.piObj (fun _ : Fin (p + 1) ↦
              (presheafToSheaf J (Type (max w v))).obj (uliftYoneda.{w}.obj x))) q).obj F),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH.{z, max w v, v, u} J n).obj F) := sorry

end CategoryTheory.Presheaf.Cech
