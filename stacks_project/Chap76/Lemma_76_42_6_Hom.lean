/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap69.Lemma_69_22_2_IdealPower
public import stacks_project.Chap76.Lemma_76_42_6_ProperOver
public import stacks_project.Chap76.«76_42_2_1_Completion»

/-!
# Hom-sets of coherent completions with proper support intersection

In Situation 76.42.5, the canonical completion functor is bijective on
morphisms between coherent modules whose supports meet in a subset proper over
`Spec A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ClosedSubset
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
open AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite type separated algebraic space over a Noetherian affine base is
Noetherian. -/
instance instIsNoetherian_of_finiteType_toBase
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (toBase X)] [Separated (toBase X)] :
    IsNoetherian X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

/-- The inverse-image ideal `I 𝒪_X` is quasi-coherent. -/
instance instIsQuasiCoherent_pullbackIdeal
    {A : Type u} [CommRing A] {I : Ideal A}
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    {f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))} :
    IsQuasiCoherent (pullbackIdeal I f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  [IsAdicComplete I A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
  [FiniteType (toBase X)] [Separated (toBase X)]

/-- In Situation 76.42.5, the map on morphisms induced by coherent completion
along `I 𝒪_X` is bijective when the intersection of supports is proper over
`Spec A`. -/
theorem homMap_bijective (ℱ 𝒢 : Coh X)
    (h_support : IsProperOver (toBase X) (moduleSupport ℱ.obj ∩ moduleSupport 𝒢.obj)) :
    Function.Bijective fun f : ℱ ⟶ 𝒢 ↦
      (functor (pullbackIdeal I (toBase X))).map f :=
  sorry

/-- In Situation 76.42.5, the map on morphisms induced by coherent completion
along `I 𝒪_X` is injective when the intersection of supports is proper over
`Spec A`. -/
theorem homMap_injective (ℱ 𝒢 : Coh X)
    (h_support : IsProperOver (toBase X) (moduleSupport ℱ.obj ∩ moduleSupport 𝒢.obj)) :
    Function.Injective fun f : ℱ ⟶ 𝒢 ↦
      (functor (pullbackIdeal I (toBase X))).map f :=
  sorry

/-- In Situation 76.42.5, the map on morphisms induced by coherent completion
along `I 𝒪_X` is surjective when the intersection of supports is proper over
`Spec A`. -/
theorem homMap_surjective (ℱ 𝒢 : Coh X)
    (h_support : IsProperOver (toBase X) (moduleSupport ℱ.obj ∩ moduleSupport 𝒢.obj)) :
    Function.Surjective fun f : ℱ ⟶ 𝒢 ↦
      (functor (pullbackIdeal I (toBase X))).map f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
