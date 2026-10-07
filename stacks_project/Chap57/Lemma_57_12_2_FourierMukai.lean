module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor
public import stacks_project.Chap56.Lemma_56_7_5_Functor
public import stacks_project.Chap57.Definition_57_10_1_Siblings

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme CategoryTheory.Functor
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
variable [Abelian (RingedSpace.Coh X.toRingedSpace)]
variable [Abelian (RingedSpace.Coh Y.toRingedSpace)]
variable [HasDerivedCategory.{u} (RingedSpace.Coh X.toRingedSpace)]
variable [HasDerivedCategory.{u} (RingedSpace.Coh Y.toRingedSpace)]

/-- A functor on bounded coherent derived categories sends the heart
`RingedSpace.Coh` into the heart when it is isomorphic, after restriction along
`DerivedCategory.Bounded.singleFunctor _ 0`, to a functor of coherent sheaves. -/
def mapsHeartToHeart
    (F : DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
      DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace)) : Prop :=
  ∃ G : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace,
    Nonempty
      (DerivedCategory.Bounded.singleFunctor (RingedSpace.Coh X.toRingedSpace) (0 : ℤ) ⋙
          F ≅
        G ⋙
          DerivedCategory.Bounded.singleFunctor (RingedSpace.Coh Y.toRingedSpace)
            (0 : ℤ))

variable [IsNoetherian X]
variable [QuasiCompact (Limits.pullback.snd x y)]
variable [QuasiSeparated (Limits.pullback.snd x y)]

/-- Restriction of the Fourier--Mukai functor of a coherent kernel to coherent
modules is additive for the `Preadditive` structure of the ambient `Abelian`
instances. -/
instance instAdditive_restrictFourierMukai (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    @Functor.Additive (RingedSpace.Coh X.toRingedSpace)
      (RingedSpace.Coh Y.toRingedSpace) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (restrictFourierMukai x y K) := sorry

/-- Restriction of the Fourier--Mukai functor of a coherent kernel preserves finite
limits. -/
instance instPreservesFiniteLimits_restrictFourierMukai
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    PreservesFiniteLimits (restrictFourierMukai x y K) := sorry

/-- Restriction of the Fourier--Mukai functor of a coherent kernel preserves finite
colimits. -/
instance instPreservesFiniteColimits_restrictFourierMukai
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    PreservesFiniteColimits (restrictFourierMukai x y K) := sorry

/-- The unbounded derived functor induced by `restrictFourierMukai`. -/
noncomputable def restrictFourierMukaiDerived (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    DerivedCategory (RingedSpace.Coh X.toRingedSpace) ⥤
      DerivedCategory (RingedSpace.Coh Y.toRingedSpace) :=
  mapDerivedCategory (restrictFourierMukai x y K)

/-- The unbounded derived Fourier--Mukai functor commutes with shifts. -/
noncomputable instance instCommShift_restrictFourierMukaiDerived
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    (restrictFourierMukaiDerived x y K).CommShift ℤ := sorry

/-- The derived Fourier--Mukai functor of a coherent kernel that is flat over `X`
with support finite over `Y` preserves boundedness. -/
theorem mapDerivedCategory_obj_mem_bounded
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K]
    (M : DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace)) :
    (t.bounded : ObjectProperty
        (DerivedCategory (RingedSpace.Coh Y.toRingedSpace)))
      ((DerivedCategory.Bounded.ι ⋙ restrictFourierMukaiDerived x y K).obj M) :=
  sorry

/-- The Fourier--Mukai functor of a coherent kernel `K` that is flat over `X` and
has support finite over `Y`, restricted to bounded coherent derived categories. -/
noncomputable def boundedCoherentFunctor (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
      DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace) :=
  (t.bounded : ObjectProperty
      (DerivedCategory (RingedSpace.Coh Y.toRingedSpace))).lift
    (DerivedCategory.Bounded.ι ⋙ restrictFourierMukaiDerived x y K)
    (fun M ↦ mapDerivedCategory_obj_mem_bounded x y K M)

/-- `boundedCoherentFunctor` commutes with the forgetful functors from bounded
derived categories. -/
theorem boundedCoherentFunctor_comp_ι (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    boundedCoherentFunctor x y K ⋙ DerivedCategory.Bounded.ι =
      DerivedCategory.Bounded.ι ⋙ restrictFourierMukaiDerived x y K := sorry

/-- The bounded coherent Fourier--Mukai functor commutes with shifts. -/
noncomputable instance instCommShift_boundedCoherentFunctor
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    (boundedCoherentFunctor x y K).CommShift ℤ := sorry

/-- The bounded coherent Fourier--Mukai functor is triangulated. -/
instance instIsTriangulated_boundedCoherentFunctor
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    (boundedCoherentFunctor x y K).IsTriangulated := sorry

/-- The bounded coherent Fourier--Mukai functor is `k`-linear. -/
instance instLinear_boundedCoherentFunctor (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K]
    [Linear k (DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace))]
    [Linear k (DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace))] :
    (boundedCoherentFunctor x y K).Linear k := sorry

/-- The bounded coherent Fourier--Mukai functor sends the heart into the heart. -/
theorem mapsHeartToHeart_boundedCoherentFunctor
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    mapsHeartToHeart (boundedCoherentFunctor x y K) := sorry

end AlgebraicGeometry.Scheme.FourierMukai
