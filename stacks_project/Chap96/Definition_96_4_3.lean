/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w uA wA

/- Definition 96.4.3: let `p : 𝒳 ⥤ Over S` be a category fibred in groupoids
over `(Sch/S)_fppf`, and let `F` be a presheaf on `𝒳`. Then `F` is a Zariski,
étale, smooth, syntomic, or fppf sheaf when it is a sheaf on the associated
site `𝒳_τ`. An fppf sheaf is also called simply a sheaf. A morphism of sheaves
is a morphism of the underlying presheaves. The categories of such sheaves are
written `Sh(𝒳_Zar)`, `Sh(𝒳_étale)`, `Sh(𝒳_smooth)`, `Sh(𝒳_syntomic)`, and
`Sh(𝒳_fppf)`. -/
@[stacks 06TR] #check (AlgebraicGeometry.FiberedInGroupoids.IsSheafFor :
  ∀ {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p],
    StandardTopology → ∀ {A : Type uA} [Category.{wA} A], (𝒳ᵒᵖ ⥤ A) → Prop)

#check (AlgebraicGeometry.FiberedInGroupoids.Sheaves :
  ∀ {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p],
    StandardTopology → ∀ (A : Type uA) [Category.{wA} A], Type (max v w uA wA))

#check (CategoryTheory.fullyFaithfulSheafToPresheaf :
  ∀ {𝒳 : Type v} [Category.{w} 𝒳] (J : GrothendieckTopology 𝒳)
    (A : Type uA) [Category.{wA} A], (sheafToPresheaf J A).FullyFaithful)
