/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap70.Lemma_70_14_4_Pullback

/-!
# Quasi-compact monomorphisms with universally injective structure sheaf maps

A quasi-compact monomorphism of algebraic spaces whose structure sheaf map remains
injective after every base change is an isomorphism, hence representable by schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.4.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact
monomorphism of algebraic spaces over `S` such that for every `T ⟶ Y` the map
`𝒪_T ⟶ f_{T,*} 𝒪_{X ×_Y T}` is injective. Then `f` is an isomorphism. -/
@[stacks 0B8B]
theorem isIso_of_quasiCompact_mono_of_universallyInjectiveStructureSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Mono f]
    (h_injective : ∀ {T : AlgebraicSpace S} (g : T ⟶ Y),
      Mono (Modules.unitToPushforwardObjUnit (pullback.snd f g))) :
    IsIso f :=
  sorry

/-- Lemma 76.4.2 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact
monomorphism of algebraic spaces over `S` such that for every `T ⟶ Y` the map
`𝒪_T ⟶ f_{T,*} 𝒪_{X ×_Y T}` is injective. Then `f` is representable by schemes. -/
@[stacks 0B8B]
theorem relativelyRepresentable_of_quasiCompact_mono_of_universallyInjectiveStructureSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Mono f]
    (h_injective : ∀ {T : AlgebraicSpace S} (g : T ⟶ Y),
      Mono (Modules.unitToPushforwardObjUnit (pullback.snd f g))) :
    yoneda.relativelyRepresentable f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
