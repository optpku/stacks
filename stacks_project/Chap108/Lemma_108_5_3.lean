module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap108.Lemma_108_5_3_Existence
public import stacks_project.Chap99.«99_8_1_1_Functor»

/-!
# Lemma 108.5.3

If `f : X ⟶ B` is proper and of finite presentation and `F` is a
quasi-coherent finite-type `𝒪_X`-module, then the Grothendieck Quot functor
`quot f F` satisfies the existence part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.5.3: if `f : X ⟶ B` is proper as well as of finite presentation
and `F` is a quasi-coherent finite-type `𝒪_X`-module, then
`quot f F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)` satisfies the existence part of
the valuative criterion (Morphisms of Spaces, Definition 67.41.1). -/
@[stacks 0DM4]
instance instExistence (f : X ⟶ B) [FinitePresentation f] [Proper f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ValuativeCriterion.Existence (quot f F) :=
  sorry

/-- The Grothendieck Quot functor satisfies the existence part of the valuative
criterion if and only if every valuative square admits a dominating extension
with a lift of the generic point. -/
theorem existence_spec (f : X ⟶ B) [FinitePresentation f] [Proper f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ValuativeCriterion.Existence (quot f F) ↔
      ∀ sq : ValuativeCommSq (quot f F), Nonempty sq.Extension :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
