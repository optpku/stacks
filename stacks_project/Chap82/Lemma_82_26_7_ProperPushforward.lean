/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_40_3_Pullback
public import stacks_project.Chap82.Definition_82_26_1_Bivariant

/-!
# Proper pushforward of bivariant classes of algebraic spaces

In Situation 82.2.1, a degree-`p` bivariant class of `f ≫ g` may be pushed
along a proper morphism `f` of good algebraic spaces, yielding a degree-`p`
bivariant class of `g` whose caps are Chow pushforward along the base change
of `f` after capping with the original class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BivariantClass

variable {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable [QuasiSeparated (g ≫ pZ)] [LocallyOfFiniteType (g ≫ pZ)]
variable [QuasiSeparated ((f ≫ g) ≫ pZ)] [LocallyOfFiniteType ((f ≫ g) ≫ pZ)]

/-- Pasting the base-change square of `f` with a cartesian square for `g`
gives the cartesian square used to evaluate a bivariant class of `f ≫ g`. -/
theorem properPushforwardSquare {Y' Z' : AlgebraicSpace S}
    (i : Y' ⟶ Y) (g' : Y' ⟶ Z') (h : Z' ⟶ Z)
    (square : IsPullback i g' g h) :
    IsPullback (pullback.fst f i) (pullback.snd f i ≫ g') (f ≫ g) h :=
  sorry

/-- Structure morphisms of the chosen fibre product of `f` along a test map
of `Y` agree after composing with `g ≫ pZ`. -/
theorem pullbackSnd_comp_structure {Y' : AlgebraicSpace S} (i : Y' ⟶ Y) :
    pullback.snd f i ≫ (i ≫ g ≫ pZ) =
      pullback.fst f i ≫ (f ≫ g) ≫ pZ :=
  sorry

/-- Quasi-separation of the structure morphism of `X ×_Y Y'` over `B`. -/
instance instQuasiSeparated_pullbackFst_comp {Y' : AlgebraicSpace S}
    (i : Y' ⟶ Y) [QuasiSeparated (i ≫ g ≫ pZ)] :
    QuasiSeparated (pullback.fst f i ≫ (f ≫ g) ≫ pZ) :=
  sorry

/-- Local finite type of the structure morphism of `X ×_Y Y'` over `B`. -/
instance instLocallyOfFiniteType_pullbackFst_comp {Y' : AlgebraicSpace S}
    (i : Y' ⟶ Y) [LocallyOfFiniteType (i ≫ g ≫ pZ)] :
    LocallyOfFiniteType (pullback.fst f i ≫ (f ≫ g) ≫ pZ) :=
  sorry

variable [Proper f]

/-- The cap family obtained by evaluating on the base change of a proper
morphism and then applying proper pushforward on Chow groups. -/
noncomputable def properPushforwardCapFamily {p : ℤ}
    (c : BivariantClass δ pZ (f ≫ g) p) : CapFamily δ pZ g p :=
  fun {Y' Z'} (i : Y' ⟶ Y) (g' : Y' ⟶ Z') (h : Z' ⟶ Z)
      [QuasiSeparated (h ≫ pZ)] [LocallyOfFiniteType (h ≫ pZ)]
      [QuasiSeparated (i ≫ g ≫ pZ)] [LocallyOfFiniteType (i ≫ g ≫ pZ)]
      (square : IsPullback i g' g h) (k : ℤ) ↦
    (Hom.properPushforward δ (pullback.fst f i ≫ (f ≫ g) ≫ pZ)
        (i ≫ g ≫ pZ) (pullback.snd f i)
        (pullbackSnd_comp_structure pZ f g i) (k - p)).comp
      (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
        ((IsPullback.of_hasPullback f i).paste_vert square) k)

/-- Unfolding of `properPushforwardCapFamily` as Chow pushforward after the
original cap on the pasted square. -/
theorem properPushforwardCapFamily_apply {Y' Z' : AlgebraicSpace S}
    {p : ℤ} (c : BivariantClass δ pZ (f ≫ g) p)
    (i : Y' ⟶ Y) (g' : Y' ⟶ Z') (h : Z' ⟶ Z)
    [QuasiSeparated (h ≫ pZ)] [LocallyOfFiniteType (h ≫ pZ)]
    [QuasiSeparated (i ≫ g ≫ pZ)] [LocallyOfFiniteType (i ≫ g ≫ pZ)]
    (square : IsPullback i g' g h) (k : ℤ) :
    properPushforwardCapFamily δ pZ f g c i g' h square k =
      (Hom.properPushforward δ (pullback.fst f i ≫ (f ≫ g) ≫ pZ)
          (i ≫ g ≫ pZ) (pullback.snd f i)
          (pullbackSnd_comp_structure pZ f g i) (k - p)).comp
        (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
          (properPushforwardSquare f g i g' h square) k) :=
  sorry

/-- The proper-pushforward cap family remains compatible with proper
pushforward. -/
theorem properPushforwardCapFamily_map_proper {p : ℤ}
    (c : BivariantClass δ pZ (f ≫ g) p) :
    CompatibleWithProperPushforward δ pZ g
      (properPushforwardCapFamily δ pZ f g c) :=
  sorry

/-- The proper-pushforward cap family remains compatible with flat
pullback. -/
theorem properPushforwardCapFamily_pullback_flat {p : ℤ}
    (c : BivariantClass δ pZ (f ≫ g) p) :
    CompatibleWithFlatPullback δ pZ g
      (properPushforwardCapFamily δ pZ f g c) :=
  sorry

/-- The proper-pushforward cap family remains compatible with Cartier
Gysin. -/
theorem properPushforwardCapFamily_gysin_cartier {p : ℤ}
    (c : BivariantClass δ pZ (f ≫ g) p) :
    CompatibleWithCartierGysin δ pZ g
      (properPushforwardCapFamily δ pZ f g c) :=
  sorry

/-- Proper pushforward of a degree-`p` bivariant class along the first
morphism in a composable pair of good algebraic spaces over `B`. -/
noncomputable def properPushforward (p : ℤ)
    (c : BivariantClass δ pZ (f ≫ g) p) : BivariantClass δ pZ g p :=
  ofCap δ pZ g (properPushforwardCapFamily δ pZ f g c)
    (properPushforwardCapFamily_map_proper δ pZ f g c)
    (properPushforwardCapFamily_pullback_flat δ pZ f g c)
    (properPushforwardCapFamily_gysin_cartier δ pZ f g c)

/-- Evaluation of proper pushforward is the original cap map followed by
Chow pushforward along the base-changed proper morphism. -/
theorem properPushforward_cap (p : ℤ) (c : BivariantClass δ pZ (f ≫ g) p)
    {Y' Z' : AlgebraicSpace S}
    (i : Y' ⟶ Y) (g' : Y' ⟶ Z') (h : Z' ⟶ Z)
    [QuasiSeparated (h ≫ pZ)] [LocallyOfFiniteType (h ≫ pZ)]
    [QuasiSeparated (i ≫ g ≫ pZ)] [LocallyOfFiniteType (i ≫ g ≫ pZ)]
    (square : IsPullback i g' g h) (k : ℤ) :
    (properPushforward δ pZ f g p c).cap i g' h square k =
      (Hom.properPushforward δ (pullback.fst f i ≫ (f ≫ g) ≫ pZ)
          (i ≫ g ≫ pZ) (pullback.snd f i)
          (pullbackSnd_comp_structure pZ f g i) (k - p)).comp
        (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
          (properPushforwardSquare f g i g' h square) k) :=
  sorry

/-- On the chosen fibre product `Y' = Y ×_Z Z'`, the cap of
`properPushforward` is Chow pushforward along the base change of `f`. -/
theorem properPushforward_cap_pullback (p : ℤ)
    (c : BivariantClass δ pZ (f ≫ g) p) {Z' : AlgebraicSpace S} (h : Z' ⟶ Z)
    [QuasiSeparated (h ≫ pZ)] [LocallyOfFiniteType (h ≫ pZ)]
    [QuasiSeparated (pullback.fst g h ≫ g ≫ pZ)]
    [LocallyOfFiniteType (pullback.fst g h ≫ g ≫ pZ)] (k : ℤ) :
    cap_pullback δ pZ g (properPushforward δ pZ f g p c) h k =
      (Hom.properPushforward δ
          (pullback.fst f (pullback.fst g h) ≫ (f ≫ g) ≫ pZ)
          (pullback.fst g h ≫ g ≫ pZ) (pullback.snd f (pullback.fst g h))
          (pullbackSnd_comp_structure pZ f g (pullback.fst g h)) (k - p)).comp
        (c.cap (pullback.fst f (pullback.fst g h))
          (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h) h
          (properPushforwardSquare f g (pullback.fst g h)
            (pullback.snd g h) h (IsPullback.of_hasPullback g h)) k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BivariantClass

