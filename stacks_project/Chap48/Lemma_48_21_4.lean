/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.TorAmplitude
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

/- Lemma 48.21.4 (1): for a flat morphism, nontrivial degree-`i` cohomology at
`x` of the compactification model of `f⁺!𝒪_Y` lies in `Set.Icc (-(d : ℤ)) 0` when
the local fibre dimension at `x` is `d`. -/
@[stacks 0BV6] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.cohomologyStalk_degree_mem_of_flat :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
      (P : Compactification.Of Y.obj.left (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint (Compactification.Of.ambientMorphism P))
      (x : X.obj.left) (d : ℕ)
      (h_dimension : fiberDimensionAt f.hom.left x = (d : WithBot ℕ∞))
      (i : ℤ)
      (hi : Nontrivial (cohomologyStalk
        (Compactification.Of.UpperShriek.dualizingObject f P A).obj i x)),
      i ∈ Set.Icc (-(d : ℤ)) 0)

/- Lemma 48.21.4 (2): if a flat morphism has all local fibre dimensions at most
`d`, then its compactification model has Tor-amplitude in `[-d, 0]` after
restriction to `f⁻¹𝒪_Y`. -/
@[stacks 0BV6] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject_hasTorAmplitudeInOver_of_flat :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
      (P : Compactification.Of Y.obj.left (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint (Compactification.Of.ambientMorphism P))
      (d : ℕ) [Scheme.Hom.RelativeDimensionLE f.hom.left d],
      HasTorAmplitudeInOver (f.hom.left).toShHom
        (Compactification.Of.UpperShriek.dualizingObject f P A).obj
          (-(d : ℤ)) 0)
