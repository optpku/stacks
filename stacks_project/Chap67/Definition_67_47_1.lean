module

public import stacks_project.Chap67.Definition_67_47_1_Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 67.47.1 (1): two morphisms from dense open subspaces of `X` into `Y` determine
the same rational map exactly when they agree on a further dense open of the intersection. -/
@[stacks 0EMM] #check
  (PartialMap.toRationalMap_eq_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f g : PartialMap X Y},
      f.toRationalMap = g.toRationalMap ↔ f.equiv g)

/- Definition 67.47.1 (2): a rational map from `X` to `Y` is an equivalence class of such
partial maps, so every rational map has a partial-map representative. -/
@[stacks 0EMM] #check
  (RationalMap.exists_rep :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y),
      ∃ f : PartialMap X Y, f.toRationalMap = φ)

/- Definition 67.47.1 (3): given morphisms `X ⟶ B` and `Y ⟶ B`, a rational map from `X` to `Y`
is a `B`-rational map exactly when it has a partial-map representative that is a morphism over
`B`. -/
@[stacks 0EMM] #check
  (RationalMap.isOver_iff_exists_partialMap_over :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} [OverClass X B] [OverClass Y B]
      (φ : RationalMap X Y),
      φ.IsOver B ↔ ∃ f : PartialMap X Y, f.IsOver B ∧ f.toRationalMap = φ)

end AlgebraicGeometry.AlgebraicSpace
