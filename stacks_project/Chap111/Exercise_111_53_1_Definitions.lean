/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Variety
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable {R : Type u} [CommRing R]
variable {k : Type u} [Field k] (V : Over (Spec (CommRingCat.of k)))

/- Exercise 111.53.1 (Definitions): the following checks cover the six requested concepts. -/
@[stacks 069R] #check (AlgebraicGeometry.Variety :
  ∀ {k : Type u} [Field k], CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) → Prop)

/- Companion concept (1): a separated scheme. -/
#check (X.IsSeparated : Prop)

#check (Scheme.isSeparated_iff X :
  X.IsSeparated ↔ IsSeparated (Limits.terminal.from X))

#check (isSeparated_iff (f := f) :
  IsSeparated f ↔ IsClosedImmersion (Limits.pullback.diagonal f))

/- Companion concept (2): a quasi-compact morphism of schemes. -/
#check (QuasiCompact f : Prop)

#check (quasiCompact_iff (f := f) :
  QuasiCompact f ↔ ∀ U : Set Y, IsOpen U → IsCompact U → IsCompact (f ⁻¹' U))

/- Companion concept (3): an affine morphism of schemes. -/
#check (IsAffineHom f : Prop)

#check (isAffineHom_iff (f := f) :
  IsAffineHom f ↔ ∀ U : Y.Opens, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U))

/- Companion concept (4): a multiplicative subset of a ring. -/
#check (Submonoid R : Type u)

#check (Submonoid.one_mem : ∀ S : Submonoid R, (1 : R) ∈ S)

#check (Submonoid.mul_mem :
  ∀ (S : Submonoid R) {x y : R}, x ∈ S → y ∈ S → x * y ∈ S)

/- Companion concept (5): a Noetherian scheme. -/
#check (IsNoetherian X : Prop)

#check (isNoetherian_iff (X := X) :
  IsNoetherian X ↔ IsLocallyNoetherian X ∧ CompactSpace X)

/- Companion concept (6): a variety over a field. -/
#check (Variety V : Prop)

#check (variety_iff V :
  Variety V ↔ IsIntegral V.left ∧ IsSeparated V.hom ∧ Scheme.Hom.FiniteType V.hom)
