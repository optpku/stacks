/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w uA wA

#check (AlgebraicGeometry.FiberedInGroupoids.IsSheafFor :
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
