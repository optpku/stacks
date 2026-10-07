module

public import stacks_project.Chap76.Lemma_76_42_1_Category

/-!
# Epimorphisms of coherent formal modules on algebraic spaces

This file characterizes epimorphisms in the category of coherent formal modules
through their first-stage components.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of coherent formal modules over a Noetherian algebraic space is an
epimorphism exactly when its component at the first stage is an epimorphism. -/
theorem coherentFormalModules_epi_iff_firstStage_epi
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    {I : IdealSubobject X} [IsQuasiCoherent I]
    {F G : CoherentFormalModules X I} (φ : F ⟶ G) :
    Epi φ ↔ Epi (φ.hom.app (Opposite.op 1)) := sorry

end AlgebraicGeometry.AlgebraicSpace
