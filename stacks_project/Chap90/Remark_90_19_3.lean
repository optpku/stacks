/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Comparison
import StacksCheckRecall

/-!
# Independence of infinitesimal automorphisms from the choice of pushforward

For a category cofibered in groupoids over `C_Λ`, the group
`infinitesimalAutomorphismsAt p x0 x0' φ` attached to a dual-number pushforward of `x0`
is independent of that pushforward up to the canonical `MulEquiv` of any two
pushforwards, and is functorial in residue-fibre isomorphisms. In particular
`Aut x0` acts by conjugation through `fiberAutHom`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open Functor Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsFibered.InGroupoids p.op]

namespace CategoryTheory.Functor

/- Remark 90.19.3 (1) -/
@[stacks 06JR] #check (CategoryTheory.Functor.infAutAtIso_of_pushforward :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ],
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      infinitesimalAutomorphismsAt p x0 y0' ψ)

#check (CategoryTheory.Functor.infAutAtIso_of_pushforward_apply :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ),
    (infAutAtIso_of_pushforward p φ ψ a).val =
      (fiberIso_of_pushforward p φ ψ).conjAut a.val)

/- Remark 90.19.3 (2) -/
@[stacks 06JR] #check (CategoryTheory.Functor.infAutAtIso_of_fiberIso :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ],
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      infinitesimalAutomorphismsAt p y0 y0' ψ)

#check (CategoryTheory.Functor.infAutAtIso_of_fiberIso_apply :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ),
    (infAutAtIso_of_fiberIso p α φ ψ a).val =
      (fiberIso_of_fiberIso p α φ ψ).conjAut a.val)

#check (CategoryTheory.Functor.infAutAtIso_of_fiberIso_independent_of_pushforward :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {x0 y0 : p.Fiber (residue Λ k)}
    {x0' x0'' y0' y0'' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (φ' : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0'')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    (ψ' : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0'')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ']
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ'],
    (infAutAtIso_of_pushforward p φ φ').trans
        (infAutAtIso_of_fiberIso p α φ' ψ') =
      (infAutAtIso_of_fiberIso p α φ ψ).trans
        (infAutAtIso_of_pushforward p ψ ψ'))

/- Remark 90.19.3 (3) -/
@[stacks 06JR] #check (CategoryTheory.Functor.instMulDistribMulAction_aut_infAutAt :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ],
    MulDistribMulAction (Aut x0) (infinitesimalAutomorphismsAt p x0 x0' φ))

#check (CategoryTheory.Functor.infAutAtIso_of_fiberIso_one_apply :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ),
    infAutAtIso_of_fiberIso p (1 : Aut x0) φ φ a = a)

#check (CategoryTheory.Functor.infAutAtIso_of_fiberIso_mul_apply :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (β γ : Aut x0) (a : infinitesimalAutomorphismsAt p x0 x0' φ),
    infAutAtIso_of_fiberIso p (β * γ) φ φ a =
      infAutAtIso_of_fiberIso p β φ φ
        (infAutAtIso_of_fiberIso p γ φ φ a))

#check (CategoryTheory.Functor.infAutAt_smul_eq_fiberAutHom_conj :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (β : Aut x0) (a : infinitesimalAutomorphismsAt p x0 x0' φ),
    (β • a).val =
      fiberAutHom p (residueToDualNumber Λ k) φ β * a.val *
        (fiberAutHom p (residueToDualNumber Λ k) φ β)⁻¹)

end CategoryTheory.Functor
