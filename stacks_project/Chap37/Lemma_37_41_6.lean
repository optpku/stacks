module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.41.6 (1): after an elementary étale base change, a separated locally finite
type morphism with finitely many isolated points in the distinguished fibre decomposes
into a finite clopen part and a clopen part whose distinguished fibre has no isolated
points. -/
@[stacks 02LP] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_decomposition_noIsolatedFiber :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f] (s : S),
      Set.Finite {x : f.fiber s | IsOpen ({x} : Set (f.fiber s))} →
        ∃ U : EtaleNeighborhood.Elementary S s,
          let E := U.obj
          let P := pullback f E.toEtale.hom
          ∃ (W V : P.Opens)
            (_ : W ⊔ V = ⊤)
            (_ : Disjoint (W : Set P) (V : Set P))
            (_ : IsClopen (W : Set P))
            (_ : IsClopen (V : Set P)),
            let pV := V.ι ≫ pullback.snd f E.toEtale.hom
            let pW := W.ι ≫ pullback.snd f E.toEtale.hom
            ∃ (_ : IsFinite pV),
              ∀ w : pW.fiber E.point,
                ¬ IsOpen ({w} : Set (pW.fiber E.point)))

/- Lemma 37.41.6 (2): if the point-set fibre is finite, the complementary clopen part
in the elementary étale decomposition can be chosen with empty distinguished fibre. -/
@[stacks 02LP] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_decomposition_emptyFiber_of_finite :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f] (s : S),
      Set.Finite (f ⁻¹' ({s} : Set S)) →
        ∃ U : EtaleNeighborhood.Elementary S s,
          let E := U.obj
          let P := pullback f E.toEtale.hom
          ∃ (W V : P.Opens)
            (_ : W ⊔ V = ⊤)
            (_ : Disjoint (W : Set P) (V : Set P))
            (_ : IsClopen (W : Set P))
            (_ : IsClopen (V : Set P)),
            let pV := V.ι ≫ pullback.snd f E.toEtale.hom
            let pW := W.ι ≫ pullback.snd f E.toEtale.hom
            ∃ (_ : IsFinite pV), IsEmpty (pW.fiber E.point))

end AlgebraicGeometry.Scheme.Hom
