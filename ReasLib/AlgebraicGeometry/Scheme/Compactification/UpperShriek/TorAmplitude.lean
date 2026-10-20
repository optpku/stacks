module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.TorAmplitude
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.FiberDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/-- For a flat morphism, nontrivial cohomology of the compactification model at a
point occurs only in degrees between the negative local fibre dimension and zero. -/
theorem cohomologyStalk_degree_mem_of_flat
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (x : X.obj.left) (d : ℕ)
    (h_dimension : fiberDimensionAt f.hom.left x = (d : WithBot ℕ∞))
    (i : ℤ)
    (hi : Nontrivial (cohomologyStalk (dualizingObject f P A).obj i x)) :
    i ∈ Set.Icc (-(d : ℤ)) 0 := sorry

/-- If a flat morphism has all local fibre dimensions at most `d`, its
compactification model has Tor-amplitude in `[-d, 0]` after relative restriction. -/
theorem dualizingObject_hasTorAmplitudeInOver_of_flat
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
    [DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase f.hom.left.toShHom))]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (d : ℕ) [Scheme.Hom.RelativeDimensionLE f.hom.left d] :
    HasTorAmplitudeInOver (f.hom.left).toShHom
      (dualizingObject f P A).obj (-(d : ℤ)) 0 := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
