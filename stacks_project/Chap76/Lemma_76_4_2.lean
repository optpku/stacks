/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism.StructureSheaf
import StacksCheckRecall

/-!
# Quasi-compact monomorphisms with universally injective structure sheaf maps

A quasi-compact monomorphism of algebraic spaces whose structure sheaf map remains
injective after every base change is an isomorphism, hence representable by schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.4.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact
monomorphism of algebraic spaces over `S` such that for every `T ⟶ Y` the map
`𝒪_T ⟶ f_{T,*} 𝒪_{X ×_Y T}` is injective. Then `f` is an isomorphism
(and hence representable by schemes). -/
@[stacks 0B8B] #check
  (AlgebraicGeometry.AlgebraicSpace.Monomorphisms.isIso_of_universallyInjectiveStructureSheaf :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Mono f]
    (h_injective : ∀ {T : AlgebraicSpace S} (g : T ⟶ Y),
      Mono (Modules.unitToPushforwardObjUnit (pullback.snd f g))),
    IsIso f)

#check
  (AlgebraicGeometry.AlgebraicSpace.Monomorphisms.relativelyRepresentable_of_universallyInjectiveStructureSheaf :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Mono f]
    (h_injective : ∀ {T : AlgebraicSpace S} (g : T ⟶ Y),
      Mono (Modules.unitToPushforwardObjUnit (pullback.snd f g))),
    yoneda.relativelyRepresentable f)

end AlgebraicGeometry.AlgebraicSpace
