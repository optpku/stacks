module

import StacksCheckRecall
public import stacks_project.Chap76.Lemma_76_42_2_Epi

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.42.2: for a scheme `S`, a Noetherian algebraic space `X` over `S`,
and a quasi-coherent ideal sheaf `I ⊂ 𝒪_X`, a morphism of coherent formal
modules is an epimorphism if and only if its first-stage component is an
epimorphism. -/
@[stacks 08B3] #check
  (coherentFormalModules_epi_iff_firstStage_epi :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      {I : IdealSubobject X} [IsQuasiCoherent I]
      {F G : CoherentFormalModules X I} (φ : F ⟶ G),
      Epi φ ↔ Epi (φ.hom.app (Opposite.op 1)))
