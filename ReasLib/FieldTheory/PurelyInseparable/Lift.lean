/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.Generated

@[expose] public section

/-!
# Finite purely inseparable lifts

This module owns the reusable field-theoretic square in which both vertical
extensions are finite purely inseparable, together with the refinement whose
lifted top extension is separably generated.  Both notions are independent of
the construction used to produce them.

@stack 04KM
-/

universe u v w x y z

namespace FieldExtension
namespace PurelyInseparable

/-- A commutative square of field extensions whose two vertical edges are finite purely
inseparable extensions. -/
@[stacks 04KM "finite purely inseparable square"]
class Square
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (k' : Type w) [Field k'] [Algebra k k']
    (K' : Type x) [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K'] : Prop where
  /-- The top vertical extension is finite dimensional. -/
  finiteDimensionalTop : FiniteDimensional K K'
  /-- The top vertical extension is purely inseparable. -/
  purelyInseparableTop : IsPurelyInseparable K K'
  /-- The base vertical extension is finite dimensional. -/
  finiteDimensionalBase : FiniteDimensional k k'
  /-- The base vertical extension is purely inseparable. -/
  purelyInseparableBase : IsPurelyInseparable k k'

namespace Square

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {k' : Type w} [Field k'] [Algebra k k']
variable {K' : Type x} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
variable [IsScalarTower k K K'] [IsScalarTower k k' K']

/-- The four defining conditions of a finite purely inseparable square. -/
@[stacks 04KM "finite purely inseparable square specification"]
theorem spec (h : Square k K k' K') :
    FiniteDimensional K K' ∧
      IsPurelyInseparable K K' ∧
        FiniteDimensional k k' ∧ IsPurelyInseparable k k' := sorry

/-- The four edge instances canonically form a finite purely inseparable square. -/
@[stacks 04KM "finite purely inseparable square constructor"]
theorem of
    [FiniteDimensional K K'] [IsPurelyInseparable K K']
    [FiniteDimensional k k'] [IsPurelyInseparable k k'] :
    Square k K k' K' := sorry

end

/-- Composing compatible finite purely inseparable squares gives a square of the composite
extension. -/
@[stacks 04KM "composition of finite purely inseparable squares"]
theorem comp
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {k' : Type w} [Field k'] [Algebra k k']
    {K' : Type x} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    {w' : Type y} [Field w'] [Algebra k' w'] [Algebra k w']
    {L : Type z} [Field L] [Algebra k L] [Algebra K L] [Algebra k' L] [Algebra K' L] [Algebra w' L]
    [IsScalarTower k K L] [IsScalarTower k k' L] [IsScalarTower k' K' L] [IsScalarTower k' w' L]
    [IsScalarTower k w' L] [IsScalarTower K K' L] [IsScalarTower k k' w']
    (h₁ : Square k K k' K') (h₂ : Square k' K' w' L) : Square k K w' L := sorry

end Square

/-- A finite purely inseparable square whose lifted top extension is separably generated over
the lifted base. -/
@[stacks 04KM "finite purely inseparable lift"]
class Lift
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (k' : Type w) [Field k'] [Algebra k k']
    (K' : Type x) [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K'] extends Square k K k' K' where
  /-- The lifted top extension is separably generated over the lifted base. -/
  separablyGeneratedTop : Algebra.IsSeparablyGenerated k' K'

namespace Lift

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {k' : Type w} [Field k'] [Algebra k k']
variable {K' : Type x} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
variable [IsScalarTower k K K'] [IsScalarTower k k' K']

/-- The five defining conditions of a finite purely inseparable lift. -/
@[stacks 04KM "finite purely inseparable lift specification"]
theorem spec (h : Lift k K k' K') :
    FiniteDimensional K K' ∧
      IsPurelyInseparable K K' ∧
        FiniteDimensional k k' ∧
          IsPurelyInseparable k k' ∧ Algebra.IsSeparablyGenerated k' K' := sorry

/-- The top edge of a finite purely inseparable lift is separable over the
lifted base. -/
@[stacks 030X "separable-over consequence of a finite purely inseparable lift"]
theorem isSeparableOver (h : Lift k K k' K') :
    Algebra.IsSeparableOver k' K' := sorry

/-- The four edge instances and separable generation canonically form a finite purely
inseparable lift. -/
@[stacks 04KM "finite purely inseparable lift constructor"]
theorem of
    [FiniteDimensional K K'] [IsPurelyInseparable K K']
    [FiniteDimensional k k'] [IsPurelyInseparable k k']
    (h : Algebra.IsSeparablyGenerated k' K') : Lift k K k' K' := sorry

end

/-- Composing two compatible finite purely inseparable lifts gives a lift of the composite
extension. -/
@[stacks 04KM "composition of finite purely inseparable lifts"]
theorem comp
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {k' : Type w} [Field k'] [Algebra k k']
    {K' : Type x} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    {w' : Type y} [Field w'] [Algebra k' w'] [Algebra k w']
    {L : Type z} [Field L] [Algebra k L] [Algebra K L] [Algebra k' L] [Algebra K' L] [Algebra w' L]
    [IsScalarTower k K L] [IsScalarTower k k' L] [IsScalarTower k' K' L] [IsScalarTower k' w' L]
    [IsScalarTower k w' L] [IsScalarTower K K' L] [IsScalarTower k k' w']
    (h₁ : Lift k K k' K') (h₂ : Lift k' K' w' L) : Lift k K w' L := sorry

/-- Precomposing a finite purely inseparable lift with a finite purely inseparable square gives
a lift of the original extension. -/
@[stacks 04KM "precomposition of a finite purely inseparable lift"]
theorem compOfSquare
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {B : Type w} [Field B] [Algebra F B]
    {L : Type x} [Field L] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    {B' : Type y} [Field B'] [Algebra F B'] [Algebra B B'] [IsScalarTower F B B']
    {L' : Type z} [Field L'] [Algebra F L'] [Algebra E L'] [Algebra B L'] [Algebra L L']
    [Algebra B' L']
    [IsScalarTower F E L'] [IsScalarTower E L L'] [IsScalarTower F B' L']
    [IsScalarTower B L L'] [IsScalarTower B B' L']
    (h : Square F E B L) (h' : Lift B L B' L') : Lift F E B' L' := sorry

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Over a perfect base field, an essentially finite-type extension admits a finite purely
inseparable lift in arbitrary requested witness universes. -/
@[stacks 04KM "identity finite purely inseparable lift over a perfect field"]
theorem existsIdentityOfPerfectField
    [PerfectField k] [Algebra.EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        Lift k K k' K' := sorry

/-- A separably generated field extension admits its identity finite purely inseparable lift in
arbitrary requested witness universes. -/
@[stacks 04KM "identity finite purely inseparable lift of a separably generated extension"]
theorem existsIdentityOfSeparablyGenerated
    (h : Algebra.IsSeparablyGenerated k K) :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        Lift k K k' K' := sorry

/-- Every essentially finite-type field extension has a finite purely inseparable lift whose
lifted top extension is separably generated. -/
@[stacks 04KM "finite purely inseparable lift to a separably generated extension"]
theorem existsOfEssFiniteType
    [Algebra.EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        Lift k K k' K' := sorry

end

end Lift

end PurelyInseparable
end FieldExtension
