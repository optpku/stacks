module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import stacks_project.Chap93.Lemma_93_10_6_Source

/-!
# Source equivalence of morphism deformation categories

If `f : X ⟶ Y` is a morphism of schemes over `k` with `f_* 𝒪_X = 𝒪_Y` and
`R¹ f_* 𝒪_X = 0`, then the forgetful morphism of deformation categories
`Def_{X ⟶ Y} ⥤ᵇ Def_X` is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped BasedFunctor

universe u

namespace FlatSchemeMorphismCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Lemma 93.10.6
In Example 93.9.1 let `f : X ⟶ Y` be a morphism of schemes over `k`. If
`f_* 𝒪_X = 𝒪_Y` and `R¹ f_* 𝒪_X = 0`, then the morphism of deformation
categories `sourceBasedFunctor Λ k X Y f hX hY hf` is an equivalence. -/
@[stacks 0E3X, instance]
instance instIsEquivalence_sourceBasedFunctor
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    [h_pushforward : IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
    [h_R1 : Fact
      (IsZero
        (RingedSpace.Hom.higherDirectImageModule f.toShHom
          (SheafOfModules.unit X.ringCatSheaf) 1))] :
    BasedFunctor.IsEquivalence (sourceBasedFunctor Λ k X Y f hX hY hf) :=
  sorry

end FlatSchemeMorphismCat
