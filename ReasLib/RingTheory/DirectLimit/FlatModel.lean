module

public import Mathlib.Algebra.Colimit.Ring
public import ReasLib.RingTheory.DirectLimit.Comparison
public import ReasLib.RingTheory.RingHom.FlatModel
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flat models at directed stages

This leaf records the source-system form of Lemma 10.168.1 (2).  It depends
only on a chosen ring direct limit, rather than on the stronger finite-type
approximation package.  The reusable square and comparison data are packaged
by `RingHom.FlatModel`.

@stack 02JO
-/

universe uR uS uI uStageR uStageS uM uStageM

namespace Ring.DirectLimit

namespace FlatModel

set_option linter.checkUnivs false in
/-- Lemma 10.168.1 (2), tag `02JO`: a finitely presented module that is flat
over the source of a finitely presented map descends to one stage of an
arbitrary chosen directed ring colimit.  The stage map and stage module remain
finitely presented, while the comparison square is returned as a reusable
`RingHom.FlatModel`. -/
@[stacks 02JO "flat finite-presentation model at a directed stage"]
theorem exists_atStage
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module S M]
    [Module.FinitePresentation S M]
    {Λ : Type uI} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type uStageR) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)
    (hf : f.FinitePresentation) (hflat : Module.FlatAlong f M) :
    ∃ i : Λ,
      let r : RStage i →+* R :=
        Ring.DirectLimit.toLimitHom RStage (fun i j h ↦ map i j h) colimitIso i
      ∃ (S₀ : Type uStageS) (_ : CommRing S₀) (stageMap : RStage i →+* S₀)
        (M₀ : Type uStageM) (_ : AddCommGroup M₀) (_ : Module S₀ M₀),
        ∃ targetMap : S₀ →+* S,
          ∃ P : RingHom.FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap,
            P.finitePresentation := sorry

end FlatModel

end Ring.DirectLimit
