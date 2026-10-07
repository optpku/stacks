module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.SourceLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 37.62.1: for two immersions of the same scheme into schemes smooth over a base,
membership of a chosen point in the Koszul-regular source locus is independent of the smooth
ambient scheme. -/
@[stacks 069E] #check
  (AlgebraicGeometry.IsKoszulRegularImmersion.mem_sourceLocus_iff_of_smooth_ambient :
    ∀ {S U P P' : Scheme.{u}} (p : P ⟶ S) (p' : P' ⟶ S)
      (i : U ⟶ P) (i' : U ⟶ P') [Smooth p] [Smooth p']
      [IsImmersion i] [IsImmersion i'] (u : U) (_ : i ≫ p = i' ≫ p'),
      u ∈ CategoryTheory.MorphismProperty.sourceLocus
        (fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) i ↔
        u ∈ CategoryTheory.MorphismProperty.sourceLocus
          (fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) i')
