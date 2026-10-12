/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 29.13.1: A morphism of schemes is quasi-affine when the inverse
image of every affine open of its target is a quasi-affine scheme. -/
@[stacks 01SK] #check (AlgebraicGeometry.quasiAffineHom_iff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), QuasiAffineHom f ↔
    ∀ U : S.Opens, IsAffineOpen U → (f ⁻¹ᵁ U).toScheme.IsQuasiAffine)

#check (AlgebraicGeometry.QuasiAffineHom :
  ∀ {X S : Scheme.{u}}, (X ⟶ S) → Prop)

#check (AlgebraicGeometry.quasiAffineHom_iff_affineOpens :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), AlgebraicGeometry.QuasiAffineHom f ↔
    ∀ U : S.affineOpens, (f ⁻¹ᵁ (U : S.Opens)).toScheme.IsQuasiAffine)
