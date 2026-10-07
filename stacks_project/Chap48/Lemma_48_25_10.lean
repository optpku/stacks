module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Gorenstein

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme.Hom TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.Compactification
open AlgebraicGeometry.Scheme.Compactification.Of
open AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

noncomputable section

universe u

/- Lemma 48.25.10 (1): For a flat morphism `f : X ⟶ Y` in
`FiniteTypeSeparatedOver S`, the morphism is Gorenstein at `x` if and only if
the compactification model of `f⁺!𝒪_Y` is locally shifted invertible on some
open neighbourhood of `x`. -/
@[stacks 0C08] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.gorensteinAt_iff_exists_open_isLocallyShiftedInvertible :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
      (P : Of Y.obj.left (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) (x : X.obj.left),
      gorensteinAt f.hom.left x ↔
        ∃ U : Scheme.Opens X.obj.left, x ∈ U ∧
          RingedSpace.ModuleDerived.IsLocallyShiftedInvertible
            (((DerivedQCoh.OpenImmersion.pullback U.ι).obj
              (dualizingObject f P A)).obj))

/- Lemma 48.25.10 (2): For a flat morphism in `FiniteTypeSeparatedOver S`, the
Gorenstein locus is open. -/
@[stacks 0C08] #check
  (AlgebraicGeometry.Scheme.Hom.isOpen_gorensteinLocus :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left],
      IsOpen (gorensteinLocus f.hom.left))
