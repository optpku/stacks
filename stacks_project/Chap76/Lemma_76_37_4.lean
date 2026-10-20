module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.DenseOpen
import StacksCheckRecall

/-!
# Extending finiteness from a dense open

A flat proper morphism of algebraic spaces is finite if it is finite after
base change to a topologically dense open subspace, and either the morphism
is locally of finite presentation or the open inclusion is quasi-compact.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.37.4. Let S be a scheme. Let f : X ⟶ Y be a flat proper
morphism of algebraic spaces over S. Let V ⟶ Y be an open subspace with
|V| ⊆ |Y| dense such that X_V ⟶ V is finite. If either f is locally of
finite presentation or V ⟶ Y is quasi-compact, then f is finite. -/
@[stacks 0B4J] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.of_restrict_of_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [Proper f] (V : OpenSubspace Y)
    (hV_dense : Dense V.pointsSet) [IsFinite (pullback.snd f V.ι)]
    (h_finitePresentation_or_quasiCompact :
      LocallyOfFinitePresentation f ∨ QuasiCompact V.ι),
    IsFinite f)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.of_restrict_of_flat_of_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [Proper f]
    [LocallyOfFinitePresentation f] (V : OpenSubspace Y)
    (hV_dense : Dense V.pointsSet) [IsFinite (pullback.snd f V.ι)],
    IsFinite f)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.of_restrict_of_flat_of_quasiCompact :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [Proper f]
    (V : OpenSubspace Y) (hV_dense : Dense V.pointsSet)
    [IsFinite (pullback.snd f V.ι)] [QuasiCompact V.ι],
    IsFinite f)

end AlgebraicGeometry.AlgebraicSpace
