/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Geometric properties of prescribed Euler-characteristic substacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The coherent-sheaf substack with prescribed Euler characteristics of perfect complexes is algebraic. -/
instance instAlgebraicStack (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    AlgebraicStack (toGroupoidsNumerical f E P hE) := sorry

/-- The inclusion of the coherent-sheaf substack with prescribed Euler characteristics is flat. -/
instance instFlat (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Hom.Flat (Numerical.ι f E P hE) := sorry

/-- The inclusion of the coherent-sheaf substack with prescribed Euler characteristics is a closed immersion. -/
instance instClosedImmersion (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Hom.ClosedImmersion (Numerical.ι f E P hE) := sorry

/-- For a finite family of perfect complexes, the inclusion of the prescribed Euler-characteristic substack is an open immersion. -/
instance instOpenImmersionOfFinite (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} [Finite I] (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    OpenImmersion (Numerical.ι f E P hE) := sorry

/-- Over a locally Noetherian base, the inclusion of the prescribed Euler-characteristic substack is an open immersion. -/
instance instOpenImmersionOfLocallyNoetherian (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B] :
    OpenImmersion (Numerical.ι f E P hE) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical
