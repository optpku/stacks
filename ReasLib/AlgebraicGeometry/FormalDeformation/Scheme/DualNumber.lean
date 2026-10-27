/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.Projection
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Module
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.At
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Dual-number deformations of schemes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open Functor.Fiber ArtinianLocalAlgCat
open scoped DualNumber

noncomputable section
universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeCat

/-- The trivial dual-number scheme `X ×_{Spec k} Spec k[ε]`. -/
def trivialScheme (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) : Scheme.{u} :=
  pullback hX (specMap (residueToDualNumber Λ k))

/-- The structure morphism of the trivial dual-number scheme over `Spec k[ε]`. -/
def trivialSchemeOver (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    trivialScheme Λ k X hX ⟶ Spec (CommRingCat.of (dualNumber Λ k).carrier) :=
  pullback.snd hX (specMap (residueToDualNumber Λ k))

/-- The projection `X' ⟶ X` of the trivial dual-number thickening. -/
def trivialSchemeProj (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    trivialScheme Λ k X hX ⟶ X :=
  pullback.fst hX (specMap (residueToDualNumber Λ k))

/-- The closed immersion of `X` into the trivial dual-number thickening. -/
def trivialSchemeImmersion (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    X ⟶ trivialScheme Λ k X hX :=
  pullback.lift (𝟙 X) (hX ≫ specMap (dualNumberToResidue Λ k)) sorry

/-- `trivialSchemeImmersion` is the section of `trivialSchemeProj` induced by `k[ε] ⟶ k`. -/
theorem trivialSchemeImmersion_comp_proj (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    trivialSchemeImmersion Λ k X hX ≫ trivialSchemeProj Λ k X hX = 𝟙 X := sorry

/-- Base change of a flat morphism along `Spec k[ε] ⟶ Spec k` remains flat. -/
instance instFlat_trivialSchemeOver (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    AlgebraicGeometry.Flat (trivialSchemeOver Λ k X hX) := sorry

/-- The trivial dual-number object `(k[ε], X')` of `FlatSchemeCat`. -/
def trivialObj (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) : FlatSchemeCat Λ k :=
  of (dualNumber Λ k) (trivialScheme Λ k X hX) (trivialSchemeOver Λ k X hX)
    (instFlat_trivialSchemeOver Λ k X hX)

/-- The trivial dual-number deformation of `x0 = (k, X)` in the fibre of `forget`. -/
def trivialDeformation (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    (forget Λ k).Fiber (dualNumber Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (trivialObj Λ k X hX) = dualNumber Λ k)

/-- The canonical strongly cocartesian pushforward of `x0` along `k ⟶ k[ε]`. -/
def trivialPushforward (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    fiberInclusion.obj (residueObj Λ k X hX) ⟶
      fiberInclusion.obj (trivialDeformation Λ k X hX) :=
  Hom.of (residueToDualNumber Λ k) (trivialSchemeProj Λ k X hX) sorry

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward
    (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    (forget Λ k).IsStronglyCocartesian (residueToDualNumber Λ k)
      (trivialPushforward Λ k X hX) := sorry

/-- Infinitesimal automorphisms of `Def_X` at the trivial dual-number pushforward. -/
abbrev inf (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) : Type u :=
  (Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X hX)
    (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX) : Type u)

/-- The tangent space `T Def_X` is the tangent space of the residue-fibre slice. -/
abbrev tangentSpace (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :=
  Functor.tangentSpaceAt (forget Λ k) (residueObj Λ k X hX)

end FlatSchemeCat
