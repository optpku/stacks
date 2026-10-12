/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Basic scheme base change

This leaf owns the pullback of a module and of an indexed open family along
an arbitrary cartesian square of schemes. Affine and field-extension base
changes are special cases.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

variable {X S S' : Scheme.{u}} {ι : Type v}

/-- The inverse-image family of opens on `X ×_S S'` obtained from an indexed family of opens on
`X`. -/
abbrev baseChangeOpenFamily
    (f : X ⟶ S) (g : S' ⟶ S) (U : ι → X.Opens) :
    ι → (pullback f g : Scheme.{u}).Opens :=
  fun i ↦ (Opens.map (pullback.fst f g).base).obj (U i)

/-- The inverse-image of an indexed open cover is an indexed open cover of the base-changed
scheme. -/
theorem isOpenCover_baseChangeOpenFamily
    (f : X ⟶ S) (g : S' ⟶ S)
    (U : ι → X.Opens) (hU : IsOpenCover U) :
    IsOpenCover (baseChangeOpenFamily f g U) := sorry

/-- Pulling an affine open family back along an affine base morphism again gives affine opens. -/
theorem isAffineOpen_baseChangeOpenFamily_of_isAffineHom
    (f : X ⟶ S) (g : S' ⟶ S) [IsAffineHom g]
    (U : ι → X.Opens) (hU_affine : ∀ i, IsAffineOpen (U i)) :
    ∀ i, IsAffineOpen (baseChangeOpenFamily f g U i) := sorry

namespace Modules

/-- The pullback of a scheme module along the first projection of an arbitrary scheme base
change. -/
abbrev baseChangeModule
    (f : X ⟶ S) (g : S' ⟶ S) (L : X.Modules) :
    (CategoryTheory.Limits.pullback f g : Scheme.{u}).Modules :=
  (Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst f g)).obj L

end Modules

end AlgebraicGeometry.Scheme
