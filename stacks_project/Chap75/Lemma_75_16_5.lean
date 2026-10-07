module

public import stacks_project.Chap75.Lemma_75_16_5_TensorAnnihilator
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory DerivedCategory.TStructure TopologicalSpace

universe u

/- Lemma 75.16.5 -/
@[stacks 0AEE] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.existsTensorAnnihilator :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [MonoidalCategory (ModuleDerived X)]
      (T : Closeds (Points X)),
      QuasiCompact (OpenSubspace.ofOpensι T.compl) →
        ∀ (P : DerivedQCoh X)
          (E : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn X
            (T : Set (Points X)))
          (α : P ⟶
            (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.inclusion X
              (T : Set (Points X))).obj E),
          ModuleDerived.IsPerfect P.obj ∨
              (IsPseudoCoherent X P.obj ∧
                (t.plus : ObjectProperty (ModuleDerived X)) E.obj) →
            ∃ (I : ModuleDerived X) (i : I ⟶ 𝟙_ (ModuleDerived X)),
              ModuleDerived.IsPerfect I ∧
                (i ⊗ₘ 𝟙 P.obj) ≫ (λ_ P.obj).hom ≫
                  (DerivedQCoh.inclusion X).map α = 0 ∧
                IsIso ((ModuleDerived.pullback (OpenSubspace.ofOpensι T.compl)).map i))
