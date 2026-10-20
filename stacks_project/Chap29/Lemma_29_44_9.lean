/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Dimension
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 29.44.9: an integral morphism of schemes does not increase topological Krull
dimension; if it is surjective, then it preserves topological Krull dimension. -/
@[stacks 0ECG] #check
  (AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsIntegralHom f],
      topologicalKrullDim X ≤ topologicalKrullDim Y)

/- The surjective clause of the dimension comparison. -/
#check
  (AlgebraicGeometry.topologicalKrullDim_eq_of_surjective_isIntegralHom :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsIntegralHom f] [AlgebraicGeometry.Surjective f],
      topologicalKrullDim X = topologicalKrullDim Y)

#check
  (RingHom.IsIntegral.ringKrullDim_le :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S},
      f.IsIntegral → ringKrullDim S ≤ ringKrullDim R)

#check
  (RingHom.IsIntegral.ringKrullDim_eq_of_injective :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S},
      f.IsIntegral → Function.Injective f → ringKrullDim R = ringKrullDim S)

#check
  (ringKrullDim_le_of_isIntegral :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [Algebra.IsIntegral R S],
      ringKrullDim S ≤ ringKrullDim R)

#check
  (ringKrullDim_eq_of_injective_algebraMap_of_isIntegral :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [Algebra.IsIntegral R S],
      Function.Injective (algebraMap R S) → ringKrullDim R = ringKrullDim S)

#check
  (Continuous.topologicalKrullDim_le_of_surjective_of_specializingMap :
    ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
      [QuasiSober Y] [T0Space Y] {f : X → Y},
      Continuous f → Function.Surjective f → SpecializingMap f →
        topologicalKrullDim Y ≤ topologicalKrullDim X)

#check
  (Continuous.topologicalKrullDim_le_of_surjective_of_generalizingMap :
    ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
      [QuasiSober Y] [T0Space Y] {f : X → Y},
      Continuous f → Function.Surjective f → GeneralizingMap f →
        topologicalKrullDim Y ≤ topologicalKrullDim X)

#check
  (Continuous.topologicalKrullDim_le_of_surjective_of_specializing_or_generalizingMap :
    ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
      [QuasiSober Y] [T0Space Y] {f : X → Y},
      Continuous f → Function.Surjective f → (SpecializingMap f ∨ GeneralizingMap f) →
        topologicalKrullDim Y ≤ topologicalKrullDim X)
