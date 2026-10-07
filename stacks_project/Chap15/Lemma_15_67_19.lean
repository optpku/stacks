module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.GlobalDimension
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.67.19

@stack 066P

The source's three consequences of a global-dimension bound are recalled from the shared owner.
-/

open CategoryTheory

universe u

/- Lemma 15.67.19 (1): every module has Tor dimension at most the global-dimension bound. -/
@[stacks 066P "Lemma 15.67.19 (1)"]
#check fun {R : Type u} [CommRing R] (d : ℕ) [HasGlobalDimensionLE R d]
    (M : ModuleCat R) ↦
  (HasGlobalDimensionLE.hasTorDimensionLE d M :
    ModuleCat.HasTorDimensionLE (R := R) M d)

/- Lemma 15.67.19 (2): bounded cohomological support gives the stated Tor-amplitude interval. -/
@[stacks 066P "Lemma 15.67.19 (2)"]
#check fun {R : Type u} [CommRing R] (d : ℕ) [HasGlobalDimensionLE R d]
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ)
    (hGE : K.IsGE a) (hLE : K.IsLE b) ↦
  (HasGlobalDimensionLE.hasTorAmplitudeIn d K a b hGE hLE :
    DerivedCategory.HasTorAmplitudeIn (R := R) K (a - (d : ℤ)) b)

/- Lemma 15.67.19 (3): finite Tor dimension is equivalent to bounded cohomology. -/
@[stacks 066P "Lemma 15.67.19 (3)"]
#check fun {R : Type u} [CommRing R] (d : ℕ) [HasGlobalDimensionLE R d]
    (K : DerivedCategory (ModuleCat R)) ↦
  (HasGlobalDimensionLE.hasFiniteTorDimension_iff_bounded d K :
    DerivedCategory.HasFiniteTorDimension (R := R) K ↔
      DerivedCategory.TStructure.t.bounded K)
