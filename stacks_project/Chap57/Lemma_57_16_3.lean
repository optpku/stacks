module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.FiberIsomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 57.16.3: -/
@[stacks 0G0Q] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isIso_baseChange_of_isIso_fiber :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (p : X ⟶ Y)
    (sq : CommSq p f g (𝟙 S)) (s : S)
    [IsNoetherian S] [IsProper f] [IsProper g] [Flat f]
    [IsIso (Scheme.Hom.fiberMap f p (𝟙 S) g sq s)],
    ∃ U : S.Opens, s ∈ U ∧
      IsIso
        (pullback.map f U.ι g U.ι p (𝟙 _) (𝟙 _)
          sq.w.symm
          ((Category.comp_id U.ι).trans (Category.id_comp U.ι).symm)))
