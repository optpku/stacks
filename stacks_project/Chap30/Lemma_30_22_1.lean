module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.ProperFlatBaseChange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 30.22.1
Let `A` be a Noetherian ring and set `S = Spec(A)`. Let `f : X ⟶ S` be a proper morphism of
schemes. Let `ℱ` be a coherent `𝒪_X`-module flat over `S`. Then `RΓ(X, ℱ)` is perfect, and its
derived scalar extension along every ring map `A → A'` is isomorphic to the derived global
sections of the base-changed module.
-/
@[stacks 07VK] #check
  (AlgebraicGeometry.Scheme.Modules.properFlatCoherent_affineBaseModuleDerivedGlobalSections :
    ∀ {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
      {X : Scheme.{u}} [IsNoetherianRing A]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      [AlgebraicGeometry.Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
      [AlgebraicGeometry.Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
      [AlgebraicGeometry.Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasPair A f]
      [AlgebraicGeometry.Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
        (AlgebraicGeometry.Scheme.AffineBaseChange.toBase A A' f)]
      [AlgebraicGeometry.Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasRightDerived A'
        (AlgebraicGeometry.Scheme.AffineBaseChange.toBase A A' f)]
      [AlgebraicGeometry.Scheme.Modules.AffineBaseModuleDerivedAdjunction.HasPair A'
        (AlgebraicGeometry.Scheme.AffineBaseChange.toBase A A' f)]
      [AlgebraicGeometry.Scheme.Modules.AffineBaseChangeDerivedCompatibility.HasScalarExtension
        A A']
      [AlgebraicGeometry.Scheme.Modules.AffineBaseChangeDerivedCompatibility.HasPullback
        A A' f]
      [AlgebraicGeometry.Scheme.Modules.AffineBaseChangeDerivedCompatibility.SourceRoute
        A A' f]
      [AlgebraicGeometry.Scheme.Modules.AffineBaseChangeDerivedCompatibility.TargetRoute
        A A' f]
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (hflat : AlgebraicGeometry.Scheme.Modules.flatOver ℱ f),
      (AlgebraicGeometry.Scheme.Modules.affineBaseModuleDerivedGlobalSections A f ℱ).IsPerfect ∧
        IsIso
          (AlgebraicGeometry.Scheme.Modules.affineBaseModuleDerivedGlobalSectionsBaseChangeMap
            A A' f ℱ))
