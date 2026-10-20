module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Linearity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FourierMukai
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction

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
    (restrictFourierMukaiDerived x y K).CommShift ℤ :=
  inferInstanceAs ((restrictFourierMukai x y K).mapDerivedCategory.CommShift ℤ)

/-- The Fourier--Mukai functor of a coherent kernel `K` that is flat over `X` and
has support finite over `Y`, restricted to bounded coherent derived categories. -/
noncomputable def boundedCoherentFunctor (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
      DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace) :=
  (t.bounded : ObjectProperty
      (DerivedCategory (RingedSpace.Coh Y.toRingedSpace))).lift
    (DerivedCategory.Bounded.ι ⋙ restrictFourierMukaiDerived x y K)
    (fun M ↦ ExactFunctor.Derived.Bounded.objMem
      (ExactFunctor.of (restrictFourierMukai x y K)) M)

/-- `boundedCoherentFunctor` commutes with the forgetful functors from bounded
derived categories. -/
theorem boundedCoherentFunctor_comp_ι (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    boundedCoherentFunctor x y K ⋙ DerivedCategory.Bounded.ι =
      DerivedCategory.Bounded.ι ⋙ restrictFourierMukaiDerived x y K := rfl

/-- The bounded coherent Fourier--Mukai functor commutes with shifts. -/
noncomputable instance instCommShift_boundedCoherentFunctor
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    (boundedCoherentFunctor x y K).CommShift ℤ := by
  unfold boundedCoherentFunctor
  infer_instance

/-- The bounded coherent Fourier--Mukai functor is triangulated. -/
theorem isTriangulated_boundedCoherentFunctor
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    (boundedCoherentFunctor x y K).IsTriangulated := by
  unfold boundedCoherentFunctor
  exact ObjectProperty.isTriangulated_lift _
    (DerivedCategory.Bounded.ι ⋙ (restrictFourierMukai x y K).mapDerivedCategory) _

/-- The bounded coherent Fourier--Mukai functor preserves the scalar actions induced by
the two structure morphisms to the spectrum of the field. -/
instance instLinearOverBoundedCoh_boundedCoherentFunctor
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    LinearOverBoundedCoh x y (boundedCoherentFunctor x y K) := sorry

/-- The bounded coherent Fourier--Mukai functor sends the heart into the heart. -/
theorem mapsHeartToHeart_boundedCoherentFunctor
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    mapsHeartToHeart (boundedCoherentFunctor x y K) := sorry

/-- After the canonical coherent inclusions into ambient module derived categories, the
bounded derived extension of the coherent transform is naturally isomorphic to derived
pullback, tensor product with the degree-zero kernel, and derived pushforward. On a
Noetherian scheme the canonical bounded coherent comparison is an equivalence, identifying
the bounded derived category of coherent modules with bounded coherent cohomology. -/
theorem boundedCoherentFunctor_ambient_iso
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    Nonempty
      (boundedCoherentFunctor x y K ⋙ DerivedCategory.Bounded.ι ⋙
          (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
            (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).ι
            (@Functor.additive_of_preserves_binary_products _ _ _ _
              Abelian.toPreadditive Abelian.toPreadditive
              (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).ι _ _ _) _ _) ≅
        (DerivedCategory.Bounded.ι ⋙
          (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι
            (@Functor.additive_of_preserves_binary_products _ _ _ _
              Abelian.toPreadditive Abelian.toPreadditive
              (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι _ _ _) _ _)) ⋙
          FourierMukai.functor x y
            ((DerivedCategory.singleFunctor
              (RingedSpace.Modules (Limits.pullback x y).toRingedSpace) (0 : ℤ)).obj
                ((Scheme.Modules.toRingedSpace (Limits.pullback x y)).obj K))) := sorry

end AlgebraicGeometry.Scheme.FourierMukai
