/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.BaseChange

@[expose] public section

open scoped TensorProduct

universe u v

namespace Connection

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {A' : Type u} [CommRing A']
variable {B' : Type v} [CommRing B'] [Algebra A' B'] [Algebra B B']
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
variable {Ω' : Type v} [AddCommGroup Ω'] [Module B' Ω'] [Module A' Ω'] [IsScalarTower A' B' Ω']
variable [Module B Ω'] [IsScalarTower B B' Ω']
variable {M : Type v} [AddCommGroup M] [Module B M]
variable {D : Derivation A B Ω} {D' : Derivation A' B' Ω'}

/-- Base change of a connection along a compatible linear map of one-forms. -/
noncomputable def baseChange (conn : Connection D M) (φ : Ω →ₗ[B] Ω')
    (hφD : ∀ b : B, φ (D b) = D' (algebraMap B B' b)) :
    Connection D' (M ⊗[B] B') :=
  scalarExtension conn φ hφD

end Connection
