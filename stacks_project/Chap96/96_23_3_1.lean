module

public import ReasLib.CategoryTheory.Sites.Cech.SpectralSequence.Terminal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe z w v u

/- 96.23.3.1: specialize to C = X.total, J = X.associatedTopology τ, and the
source atlas object x. For τ étale or fppf, the source establishes local
surjectivity of h_x ⟶ * using a smooth surjective atlas. The sheaf h_{x,p}
is the (p+1)-fold product of the sheafified representable h_x. For every
abelian sheaf F, the first-quadrant spectral sequence has
E₁^{p,q} = H^q(h_{x,p}, F) and converges to H^{p+q}(𝒳_τ, F). -/
@[stacks 07AL] #check
  (CategoryTheory.Presheaf.Cech.exists_spectralSequence_yoneda :
    ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
      [HasSheafify J (Type (max w v))]
      [HasSheafify J AddCommGrpCat.{max w v}]
      [HasExt.{z} (Sheaf J AddCommGrpCat.{max w v})]
      (x : C)
      [Presheaf.IsLocallySurjective J
        ((Presheaf.terminalIsTerminal.{max w v} C).from (uliftYoneda.{w}.obj x))]
      (F : Sheaf J AddCommGrpCat.{max w v}),
      ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{z} 1)
        (pageOneIso : ∀ p q : ℕ,
          (E.page 1 le_rfl).X (p, q) ≅
            (Sheaf.cohomologyOverSheafFunctor
              (Limits.piObj (fun _ : Fin (p + 1) ↦
                (presheafToSheaf J (Type (max w v))).obj (uliftYoneda.{w}.obj x))) q).obj F),
        CohomologicalSpectralSequenceNat.ConvergesTo E
          (fun n ↦ (Sheaf.functorH.{z, max w v, v, u} J n).obj F))
