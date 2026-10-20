module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.TopologicalInvariance
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 58.8.1 (1): an equivalence on finite étale schemes induces a
homeomorphism on connected components. -/
@[stacks 0BQA] #check
  (AlgebraicGeometry.Scheme.connectedComponentsHomeomorph_of_finiteEtaleBaseChange :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y),
      [Functor.IsEquivalence (Scheme.finiteEtaleBaseChange f)] →
      IsHomeomorph f.continuous.connectedComponentsMap)

/- Lemma 58.8.1 (2): in the connected case, the induced map on étale
fundamental groups at a geometric point and its image is a homeomorphism. -/
@[stacks 0BQA] #check
  (AlgebraicGeometry.Scheme.fundamentalGroupIso_of_finiteEtaleBaseChange :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y),
      [Functor.IsEquivalence (Scheme.finiteEtaleBaseChange f)] → [ConnectedSpace X] →
      ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      IsHomeomorph (AlgebraicGeometry.Scheme.Hom.fundamentalGroupMap f s))
