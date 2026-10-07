module

public import stacks_project.Chap69.Lemma_69_5_3_Hom
public import stacks_project.Chap69.Lemma_69_5_3_TestSet
import StacksCheckRecall

/-!
# Lemma 69.5.3

Hom out of a finitely presented module on a qcqs algebraic space commutes with filtered
colimits of `𝒪_X`-modules, and in particular with filtered colimits in `QCoh(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.5.3 (1): let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `G` be a finitely presented `𝒪_X`-module. Then
`Hom_X(G, -)` commutes with filtered colimits of arbitrary `𝒪_X`-modules. -/
@[stacks 07U7]
#check
  (Modules.homComparison_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
      (G : X.Modules) [G.IsFinitePresentation] (F : Λ ⥤ X.Modules)
      [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))],
      IsIso (Modules.homComparison G F))

@[stacks 07U7]
#check
  (Modules.isFinitelyPresentable :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (G : X.Modules) [G.IsFinitePresentation],
      IsFinitelyPresentable.{u + 1} G)

/- Lemma 69.5.3 (2): in particular, `Hom_X(G, -)` commutes with filtered colimits in
`QCoh(𝒪_X)`. -/
@[stacks 07U7]
#check
  (QCoh.isFinitelyPresentable :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (G : QCoh X) [G.obj.IsFinitePresentation],
      IsFinitelyPresentable.{u + 1} G)
