/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.DescentLocus
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Let `X' ⟶ X` be a morphism over `S`, with both structure maps flat, proper, and
finitely presented and with structure-sheaf units that are isomorphisms after every base
change. If finitely presented immersions `Z ⟶ S` and `Z' ⟶ S` represent the descent loci
of an invertible module and its pullback, then an inclusion `Z ⟶ Z'` is an isomorphism near
any point of `Z` where the induced map `H¹(X_s, 𝒪) ⟶ H¹(X'_s, 𝒪)` is injective. -/
theorem descentLoci_eq_near_of_fiberH1_injective
    {X' X S Z Z' : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ S) (f : X ⟶ S)
    (sq : CommSq p f' f (𝟙 S))
    [Flat f'] [IsProper f'] [Scheme.Hom.FinitePresentation f']
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (h_unit' : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f' g).toRingCatSheafHom))
    (h_unit : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f g).toRingCatSheafHom))
    (L : X.Modules) [Invertible L]
    (j : Z ⟶ S) [IsImmersion j] [Scheme.Hom.FinitePresentation j]
    (j' : Z' ⟶ S) [IsImmersion j'] [Scheme.Hom.FinitePresentation j']
    (hZ : RepresentsDescentLocus f L j)
    (hZ' : RepresentsDescentLocus f' ((Scheme.Modules.pullback p).obj L) j')
    (i : Z ⟶ Z') (h_i : i ≫ j' = j) (s : S) (h_s : s ∈ Set.range j.base)
    (hH1 : Function.Injective
      ((Scheme.Hom.fiberMap f' p (𝟙 S) f sq s).structureSheafCohomologyMap 1)) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso (i ∣_ (j' ⁻¹ᵁ U)) := sorry

/-- For a finite family of morphisms `Xᵢ i ⟶ X` over `S`, suppose `Z` and `Zᵢ i`
represent the descent loci of an invertible module and its pullbacks, with `Z` mapping
into every `Zᵢ i`. If the combined map from `H¹(X_s, 𝒪)` to the family of
`H¹(Xᵢ_s, 𝒪)` is injective, then near `s` a test scheme factors through `Z` exactly
when it factors through every `Zᵢ i`. -/
theorem descentLocus_eq_iInter_near_of_fiberH1_injective
    (n : ℕ) {X S Z : Scheme.{u}} (Xᵢ Zᵢ : Fin n → Scheme.{u})
    (p : ∀ i, Xᵢ i ⟶ X) (fᵢ : ∀ i, Xᵢ i ⟶ S) (f : X ⟶ S)
    (sq : ∀ i, CommSq (p i) (fᵢ i) f (𝟙 S))
    [∀ i, Flat (fᵢ i)] [∀ i, IsProper (fᵢ i)]
    [∀ i, Scheme.Hom.FinitePresentation (fᵢ i)]
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (h_unitᵢ : ∀ i {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd (fᵢ i) g).toRingCatSheafHom))
    (h_unit : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f g).toRingCatSheafHom))
    (L : X.Modules) [Invertible L]
    (j : Z ⟶ S) [IsImmersion j] [Scheme.Hom.FinitePresentation j]
    (jᵢ : ∀ i, Zᵢ i ⟶ S) [∀ i, IsImmersion (jᵢ i)]
    [∀ i, Scheme.Hom.FinitePresentation (jᵢ i)]
    (hZ : RepresentsDescentLocus f L j)
    (hZᵢ : ∀ i, RepresentsDescentLocus (fᵢ i)
      ((Scheme.Modules.pullback (p i)).obj L) (jᵢ i))
    (inc : ∀ i, Z ⟶ Zᵢ i) (h_inc : ∀ i, inc i ≫ jᵢ i = j)
    (s : S) (h_s : s ∈ Set.range j.base)
    (hH1 : Function.Injective (fun x ↦ fun i ↦
      ((Scheme.Hom.fiberMap (fᵢ i) (p i) (𝟙 S) f (sq i) s).structureSheafCohomologyMap
        1) x)) :
    ∃ U : S.Opens, s ∈ U ∧ ∀ {T : Scheme.{u}} (g : T ⟶ U.toScheme),
      Nonempty (Over.mk g ⟶ Over.mk (j ∣_ U)) ↔
        ∀ i, Nonempty (Over.mk g ⟶ Over.mk (jᵢ i ∣_ U)) := sorry

end AlgebraicGeometry.Scheme.Modules
