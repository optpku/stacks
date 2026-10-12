/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tor of modules on a ringed space

@stack 08BP

The default ringed-space Tor object uses the genuine two-variable derived tensor owner.  Explicit
`torLeft` and `torRight` views are available when only a fixed-factor model is needed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

section Bifunctor

variable {X : RingedSpace.{u}}
variable [hTensor : Tensor.Has X]

include hTensor

/-- The two-variable Tor functor on derived `𝒪_X`-modules. -/
@[stacks 08BP "ringed-space Tor functor"]
noncomputable abbrev torFunctor (p : ℕ) :
    ModuleDerived X × ModuleDerived X ⥤ Modules X :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.torFunctor (C := Modules X) p

/-- The `p`-th Tor object of arbitrary derived `𝒪_X`-modules. -/
@[stacks 08BP "Tor of derived module objects"]
noncomputable abbrev torObj (p : ℕ) (K L : ModuleDerived X) : Modules X :=
  (torFunctor p).obj (K, L)

/-- The `p`-th Tor object of two ordinary `𝒪_X`-modules. -/
@[stacks 08BP "Tor of two ringed-space modules"]
noncomputable abbrev tor (p : ℕ) (F G : Modules X) : Modules X :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.tor (C := Modules X) p F G

end Bifunctor

section OneSided

variable {X : RingedSpace.{u}}

/-- The fixed-right Tor functor on derived `𝒪_X`-modules. -/
@[stacks 08BP "ringed-space fixed-right Tor functor"]
noncomputable abbrev torRightFunctor (p : ℕ) (L : ModuleDerived X)
    [DerivedCategory.DerivedTensor.Right.Has (C := Modules X)] :
    ModuleDerived X ⥤ Modules X :=
  CategoryTheory.DerivedCategory.DerivedTensor.torRightFunctor (C := Modules X) p L

/-- The fixed-right presentation of Tor for arbitrary derived module objects. -/
@[stacks 08BP "ringed-space fixed-right Tor object"]
noncomputable abbrev torRightObj (p : ℕ) (K L : ModuleDerived X)
    [DerivedCategory.DerivedTensor.Right.Has (C := Modules X)] : Modules X :=
  (torRightFunctor p L).obj K

/-- The fixed-right presentation of Tor for ordinary module objects. -/
@[stacks 08BP "ringed-space degree-zero fixed-right Tor"]
noncomputable abbrev torRight (p : ℕ) (F G : Modules X)
    [DerivedCategory.DerivedTensor.Right.Has (C := Modules X)] : Modules X :=
  CategoryTheory.DerivedCategory.DerivedTensor.torRight (C := Modules X) p F G

/-- The fixed-left Tor functor on derived `𝒪_X`-modules. -/
@[stacks 08BP "ringed-space fixed-left Tor functor"]
noncomputable abbrev torLeftFunctor (p : ℕ) (K : ModuleDerived X)
    [DerivedCategory.DerivedTensor.Left.Has (C := Modules X)] :
    ModuleDerived X ⥤ Modules X :=
  CategoryTheory.DerivedCategory.DerivedTensor.torLeftFunctor (C := Modules X) p K

/-- The fixed-left presentation of Tor for arbitrary derived module objects. -/
@[stacks 08BP "ringed-space fixed-left Tor object"]
noncomputable abbrev torLeftObj (p : ℕ) (K L : ModuleDerived X)
    [DerivedCategory.DerivedTensor.Left.Has (C := Modules X)] : Modules X :=
  (torLeftFunctor p K).obj L

/-- The fixed-left presentation of Tor for ordinary module objects. -/
@[stacks 08BP "ringed-space degree-zero fixed-left Tor"]
noncomputable abbrev torLeft (p : ℕ) (F G : Modules X)
    [DerivedCategory.DerivedTensor.Left.Has (C := Modules X)] : Modules X :=
  CategoryTheory.DerivedCategory.DerivedTensor.torLeft (C := Modules X) p F G

end OneSided

end AlgebraicGeometry.RingedSpace.ModuleDerived

end
