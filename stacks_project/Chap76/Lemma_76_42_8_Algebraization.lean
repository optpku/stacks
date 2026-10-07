module

public import stacks_project.Chap76.Lemma_76_42_8_Annihilation
public import stacks_project.Chap76.Lemma_76_42_8_Completion

/-!
# Algebraization of maps of coherent formal modules on algebraic spaces

This file records algebraization data and uniqueness for maps from coherent
formal modules to completions of coherent modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Algebraization data for a morphism from a coherent formal module to the
completion of a coherent module. -/
structure FormalMapToCompletionAlgebraization {S : Scheme.{u}}
    {X : AlgebraicSpace S} {I : IdealSubobject X}
    (ctx : CoherentCompletionFunctor X I) (E : CoherentFormalModules X I)
    (G : Coh X) (alpha : E ⟶ ctx.obj G) where
  /-- The coherent module underlying the algebraization. -/
  F : Coh X
  /-- The morphism from the algebraized coherent module to the target coherent
  module. -/
  a : F ⟶ G
  /-- The underlying module morphism has ideal-power-torsion kernel and
  cokernel. -/
  torsion : Modules.HasIdealPowerTorsionKernelCokernel I
    ((Coh.inclusion X).map a)
  /-- The given formal module is isomorphic to the completion of the
  algebraized module. -/
  beta : E ≅ ctx.obj F
  /-- The formal morphism is induced by the algebraized morphism through the
  isomorphism. -/
  comm : alpha = beta.hom ≫ ctx.map a

namespace FormalMapToCompletionAlgebraization

/-- Assemble algebraization data from a coherent module, a torsion morphism to
the target, a completion isomorphism, and the commuting triangle. -/
noncomputable def of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} {ctx : CoherentCompletionFunctor X I}
    {E : CoherentFormalModules X I} {G : Coh X} {alpha : E ⟶ ctx.obj G}
    (F : Coh X) (a : F ⟶ G)
    (torsion : Modules.HasIdealPowerTorsionKernelCokernel I
      ((Coh.inclusion X).map a))
    (beta : E ≅ ctx.obj F) (comm : alpha = beta.hom ≫ ctx.map a) :
    FormalMapToCompletionAlgebraization ctx E G alpha where
  F := F
  a := a
  torsion := torsion
  beta := beta
  comm := comm

/-- An isomorphism between algebraizations of a map to a completion is
compatible when it intertwines their algebraized maps and completion
isomorphisms. -/
def IsomorphismCompatible {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} {ctx : CoherentCompletionFunctor X I}
    {E : CoherentFormalModules X I} {G : Coh X} {alpha : E ⟶ ctx.obj G}
    (z z' : FormalMapToCompletionAlgebraization ctx E G alpha)
    (e : z.F ≅ z'.F) : Prop :=
  e.hom ≫ z'.a = z.a ∧ z.beta.hom ≫ ctx.map e.hom = z'.beta.hom

/-- Compatibility of an isomorphism between algebraizations unfolds to its two
intertwining equations. -/
theorem isomorphismCompatible_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} {ctx : CoherentCompletionFunctor X I}
    {E : CoherentFormalModules X I} {G : Coh X} {alpha : E ⟶ ctx.obj G}
    (z z' : FormalMapToCompletionAlgebraization ctx E G alpha)
    (e : z.F ≅ z'.F) :
    IsomorphismCompatible z z' e ↔
      e.hom ≫ z'.a = z.a ∧ z.beta.hom ≫ ctx.map e.hom = z'.beta.hom :=
  Iff.rfl

end FormalMapToCompletionAlgebraization

/-- A coherent-formal morphism to the completion of a coherent module whose
stagewise kernels and cokernels are uniformly annihilated by an ideal power has
an algebraization, unique up to a unique compatible isomorphism. -/
theorem existsUnique_algebraization_of_formalMap_to_completion
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    {I : IdealSubobject X} [IsQuasiCoherent I]
    (ctx : CoherentCompletionFunctor X I) (E : CoherentFormalModules X I)
    (G : Coh X) (alpha : E ⟶ ctx.obj G)
    (halpha : CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation I
      alpha) :
    ∃ z : FormalMapToCompletionAlgebraization ctx E G alpha,
      ∀ z' : FormalMapToCompletionAlgebraization ctx E G alpha,
        ∃! e : z.F ≅ z'.F,
          FormalMapToCompletionAlgebraization.IsomorphismCompatible z z' e :=
  sorry

namespace CoherentCompletion

/-- A map to a canonical completion with uniformly ideal-power annihilated
stagewise kernel and cokernel has a unique algebraization. -/
theorem existsUnique_algebraization_to
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    {I : IdealSubobject X} [IsQuasiCoherent I]
    (E : CoherentFormalModules X I) (G : Coh X)
    (alpha : E ⟶ (functor I).obj G)
    (halpha : CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation I
      alpha) :
    ∃ z : FormalMapToCompletionAlgebraization
        (CoherentCompletionFunctor.canonical X I) E G alpha,
      ∀ z' : FormalMapToCompletionAlgebraization
          (CoherentCompletionFunctor.canonical X I) E G alpha,
        ∃! e : z.F ≅ z'.F,
          FormalMapToCompletionAlgebraization.IsomorphismCompatible z z' e :=
  sorry

end CoherentCompletion

end AlgebraicGeometry.AlgebraicSpace
