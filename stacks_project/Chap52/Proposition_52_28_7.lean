module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.AmpleDepth
public import stacks_project.Chap52.Proposition_52_28_7_Instances
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.CoherentCompletion

noncomputable section

@[expose] public section

universe u

/- Proposition 52.28.7 (1) -/
@[stacks 0EL7] #check
  (AlgebraicGeometry.Scheme.CoherentCompletion.neighborhoodFullyFaithful_of_depth :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat (moduleDepth (SchemeOverField.stalkRing P x)
        (SchemeOverField.stalkRing P x)) : WithTop ℤ) : WithBot (WithTop ℤ)) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) > (2 : EInt)),
    NeighborhoodCompletionFullyFaithful (zeroIdealSheaf L s))

/- Proposition 52.28.7 (2) -/
@[stacks 0EL7] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.existsFiniteLocallyFreeAlgebraization :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat (moduleDepth (SchemeOverField.stalkRing P x)
        (SchemeOverField.stalkRing P x)) : WithTop ℤ) : WithBot (WithTop ℤ)) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) > (2 : EInt))
    (F : CoherentFormalModules P.left (zeroIdealSheaf L s))
    (h_stage : ∀ n : ℕ, CoherentFormalModules.IsFiniteLocallyFreeStage F n),
      ∃ V : (compactSupport (zeroIdealSheaf L s)).openNhds,
        (onFiniteLocallyFree ((zeroIdealSheaf L s).comap
          (P.left.ofRestrict V.val.isOpenEmbedding))).essImage
            ((coherentFormalModulesRestrictionFunctor (zeroIdealSheaf L s) V.val).obj F))
