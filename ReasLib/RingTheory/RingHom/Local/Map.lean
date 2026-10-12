/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bundled local algebra homomorphisms

An explicit local algebra homomorphism packages an `R`-algebra homomorphism together with the
`IsLocalHom` condition. The map-level condition does not require local-ring structures or a
particular geometric construction.
-/

universe u v w x

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

/-- An explicit `R`-algebra homomorphism whose underlying ring
homomorphism is local.  This is a data package rather than a typeclass: a
single pair of algebras can have many local algebra homomorphisms. -/
@[stacks 08HU "explicit local algebra map"]
structure Local where
  /-- The underlying algebra homomorphism. -/
  hom : A →ₐ[R] B
  /-- The underlying ring homomorphism reflects units. -/
  isLocal : IsLocalHom hom.toRingHom

end AlgHom

namespace AlgHom.Local

section Semiring

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

/-- Explicit local algebra maps are equal as soon as their underlying
algebra homomorphisms are equal.  The `IsLocalHom` field is proposition-valued
and hence carries no additional equality data. -/
@[ext, stacks 08HU "extensionality for explicit local algebra maps"]
theorem ext {f g : AlgHom.Local (R := R) (A := A) (B := B)}
    (h : f.hom = g.hom) : f = g := sorry

end Semiring

section Composition

variable {R : Type u} {A : Type v} {B : Type w} {C : Type x}
variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- The composite of two explicit local `R`-algebra maps is local.
This is the bundled form of Mathlib's closure theorem for `IsLocalHom`; it
does not install either localness fact as an ambient instance. -/
@[stacks 08HU "locality of a composite explicit algebra map"]
theorem comp_isLocal
    (g : AlgHom.Local (R := R) (A := B) (B := C))
    (f : AlgHom.Local (R := R) (A := A) (B := B)) :
    IsLocalHom (g.hom.comp f.hom).toRingHom := sorry

/-- Compose explicit local algebra maps over one fixed base.  The
result remains explicit because neither the composite nor its induced algebra
structure is generally canonical for the underlying pair of rings. -/
@[stacks 08HU "composition of explicit local algebra maps"]
def comp
    (g : AlgHom.Local (R := R) (A := B) (B := C))
    (f : AlgHom.Local (R := R) (A := A) (B := B)) :
    AlgHom.Local (R := R) (A := A) (B := C) where
  hom := g.hom.comp f.hom
  isLocal := comp_isLocal (R := R) g f

/-- The algebra-homomorphism component of an explicit composite is
the ordinary composite of its components. -/
@[simp, stacks 08HU "underlying hom of a composite local algebra map"]
theorem comp_hom
    (g : AlgHom.Local (R := R) (A := B) (B := C))
    (f : AlgHom.Local (R := R) (A := A) (B := B)) :
    (g.comp f).hom = g.hom.comp f.hom := sorry

end Composition

section Commutative

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra R B]

/-- The named, explicit `A`-algebra structure on `B` induced by a
local `R`-algebra map.  This is deliberately not an instance, since a pair of
rings can admit several such maps. -/
@[reducible, stacks 08HU "algebra structure induced by an explicit local map"]
def toAlgebra (f : AlgHom.Local (R := R) (A := A) (B := B)) : Algebra A B :=
  f.hom.toRingHom.toAlgebra

/-- The algebra map of `Local.toAlgebra f` is the underlying ring
homomorphism of `f`. -/
@[simp, stacks 08HU "algebra map induced by an explicit local map"]
theorem algebraMap_toAlgebra (f : AlgHom.Local (R := R) (A := A) (B := B)) :
    @algebraMap A B _ _ f.toAlgebra = f.hom.toRingHom := sorry

/-- After installing `Local.toAlgebra f` explicitly, its algebra map
is local.  This remains a theorem rather than an instance because the algebra
structure is selected by the explicit map `f`. -/
@[stacks 08HU "locality of the induced algebra map"]
theorem algebraMap_isLocalHom (f : AlgHom.Local (R := R) (A := A) (B := B)) :
    IsLocalHom (@algebraMap A B _ _ f.toAlgebra) := sorry

end Commutative

section RestrictScalars

variable {R : Type u} {S : Type v} {A : Type w} {B : Type x}
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

/-- Restriction along a scalar tower preserves an explicit local
algebra map.  Its localness proof is the same proof for the unchanged
underlying ring homomorphism. -/
@[stacks 08HU "restriction of an explicit local algebra map"]
def restrictScalars (f : AlgHom.Local (R := S) (A := A) (B := B)) :
    AlgHom.Local (R := R) (A := A) (B := B) where
  hom := f.hom.restrictScalars R
  isLocal := f.isLocal

/-- The algebra-homomorphism component of scalar restriction is
Mathlib's `AlgHom.restrictScalars`. -/
@[simp, stacks 08HU "underlying hom after scalar restriction"]
theorem restrictScalars_hom (f : AlgHom.Local (R := S) (A := A) (B := B)) :
    (f.restrictScalars (R := R)).hom = f.hom.restrictScalars R := sorry

end RestrictScalars

end AlgHom.Local
