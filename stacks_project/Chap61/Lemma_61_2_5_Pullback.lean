/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ConnectedComponents.Pullback

/-!
# Connected-components pullbacks

The cartesian pullback of `ConnectedComponents.mk : X → ConnectedComponents X`
along a continuous map `T → ConnectedComponents X`, realized as the equalizer
subtype of `X × T`.
-/

@[expose] public section

universe u v w

namespace ConnectedComponents

variable {X : Type u} {T : Type v} [TopologicalSpace X] [TopologicalSpace T]

#check (ConnectedComponents.pullback : C(T, ConnectedComponents X) → Type (max u v))

variable {f : C(T, ConnectedComponents X)}

#check (ConnectedComponents.pullback.fst : pullback f → X)

#check (ConnectedComponents.pullback.snd : pullback f → T)

#check (ConnectedComponents.pullback.mk_fst_eq :
  ∀ point : pullback f, mk (pullback.fst point) = f (pullback.snd point))

#check (ConnectedComponents.pullback.continuous_fst : Continuous (pullback.fst : pullback f → X))

#check (ConnectedComponents.pullback.continuous_snd : Continuous (pullback.snd : pullback f → T))

#check (ConnectedComponents.pullback.comparison :
  ∀ {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : Y → T},
    (∀ y, mk (g y) = f (p y)) → Y → pullback f)

#check (ConnectedComponents.pullback.comparison_fst :
  ∀ {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : Y → T}
    (hcomm : ∀ y, mk (g y) = f (p y)) (y : Y),
    pullback.fst (pullback.comparison hcomm y) = g y)

#check (ConnectedComponents.pullback.comparison_snd :
  ∀ {Y : Type w} [TopologicalSpace Y] {g : Y → X} {p : Y → T}
    (hcomm : ∀ y, mk (g y) = f (p y)) (y : Y),
    pullback.snd (pullback.comparison hcomm y) = p y)

#check (ConnectedComponents.pullback.isClosed :
  ∀ [SpectralSpace X], IsClosed {point : X × T | mk point.1 = f point.2})

end ConnectedComponents
