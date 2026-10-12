/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Preservation of finite nonempty limits and colimits

The aggregate classes are universe-stable and project automatically to each finite nonempty
shape. Binary (co)products together with the finite connected preservation classes form the
canonical construction interface.
-/

@[expose] public section

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A functor preserves finite nonempty limits if it preserves limits of every finite nonempty
shape. -/
class PreservesFiniteNonemptyLimits (F : C ⥤ D) : Prop where
  /-- The functor preserves limits of every `Type`-small finite nonempty shape. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesLimitsOfShape J F

namespace PreservesFiniteNonemptyLimits

/-- Preservation of finite nonempty limits supplies preservation for finite nonempty shapes in
every universe. -/
instance (priority := 95) preservesLimitsOfShape
    (F : C ⥤ D) [PreservesFiniteNonemptyLimits F]
    (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesLimitsOfShape J F := sorry

/-- Preservation of all finite limits implies preservation of finite nonempty limits. -/
instance (priority := 100) ofFiniteLimits
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteNonemptyLimits F := sorry

/-- A composite of functors preserving finite nonempty limits preserves them. -/
instance (priority := 40) comp
    (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteNonemptyLimits F] [PreservesFiniteNonemptyLimits G] :
    PreservesFiniteNonemptyLimits (F ⋙ G) := sorry

/-- Preservation of finite nonempty limits transfers across a natural isomorphism. -/
theorem ofIso {F G : C ⥤ D} (e : F ≅ G) [PreservesFiniteNonemptyLimits F] :
    PreservesFiniteNonemptyLimits G := sorry

/-- Preservation of finite nonempty limits is invariant under natural isomorphism. -/
theorem iff_ofIso {F G : C ⥤ D} (e : F ≅ G) :
    PreservesFiniteNonemptyLimits F ↔ PreservesFiniteNonemptyLimits G := sorry

/-- Construct preservation of finite nonempty limits by supplying it in any one universe. -/
theorem ofSize
    (F : C ⥤ D)
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
      PreservesLimitsOfShape J F) :
    PreservesFiniteNonemptyLimits F := sorry

/-- A functor preserves finite nonempty limits if and only if it preserves every finite nonempty
shape in any fixed universe. -/
theorem iff_preservesLimitsOfShape (F : C ⥤ D) :
    PreservesFiniteNonemptyLimits F ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
        PreservesLimitsOfShape J F := sorry

/-- Preservation of finite nonempty limits includes preservation of finite connected limits. -/
instance (priority := 90) preservesFiniteConnectedLimits
    (F : C ⥤ D) [PreservesFiniteNonemptyLimits F] :
    PreservesFiniteConnectedLimits F := sorry

namespace BinaryProducts

/-- Preservation of binary products and finite connected limits gives preservation of all finite
nonempty limits. -/
theorem ofFiniteConnected
    (F : C ⥤ D) [HasFiniteNonemptyLimits C]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesFiniteConnectedLimits F] :
    PreservesFiniteNonemptyLimits F := sorry

/-- For a functor whose source has finite nonempty limits, preservation of those limits is
equivalent to preservation of binary products and finite connected limits. -/
theorem iff_finiteConnected
    (F : C ⥤ D) [HasFiniteNonemptyLimits C] :
    PreservesFiniteNonemptyLimits F ↔
      PreservesLimitsOfShape (Discrete WalkingPair) F ∧
        PreservesFiniteConnectedLimits F := sorry

end BinaryProducts

end PreservesFiniteNonemptyLimits

/-- A functor preserves finite nonempty colimits if it preserves colimits of every finite nonempty
shape. -/
class PreservesFiniteNonemptyColimits (F : C ⥤ D) : Prop where
  /-- The functor preserves colimits of every `Type`-small finite nonempty shape. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesColimitsOfShape J F

namespace PreservesFiniteNonemptyColimits

/-- Preservation of finite nonempty colimits supplies preservation for finite nonempty shapes in
every universe. -/
instance (priority := 95) preservesColimitsOfShape
    (F : C ⥤ D) [PreservesFiniteNonemptyColimits F]
    (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesColimitsOfShape J F := sorry

/-- Preservation of all finite colimits implies preservation of finite nonempty colimits. -/
instance (priority := 100) ofFiniteColimits
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteNonemptyColimits F := sorry

/-- A composite of functors preserving finite nonempty colimits preserves them. -/
instance (priority := 40) comp
    (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteNonemptyColimits F] [PreservesFiniteNonemptyColimits G] :
    PreservesFiniteNonemptyColimits (F ⋙ G) := sorry

/-- Preservation of finite nonempty colimits transfers across a natural isomorphism. -/
theorem ofIso {F G : C ⥤ D} (e : F ≅ G) [PreservesFiniteNonemptyColimits F] :
    PreservesFiniteNonemptyColimits G := sorry

/-- Preservation of finite nonempty colimits is invariant under natural isomorphism. -/
theorem iff_ofIso {F G : C ⥤ D} (e : F ≅ G) :
    PreservesFiniteNonemptyColimits F ↔ PreservesFiniteNonemptyColimits G := sorry

/-- Construct preservation of finite nonempty colimits by supplying it in any one universe. -/
theorem ofSize
    (F : C ⥤ D)
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
      PreservesColimitsOfShape J F) :
    PreservesFiniteNonemptyColimits F := sorry

/-- A functor preserves finite nonempty colimits if and only if it preserves every finite nonempty
shape in any fixed universe. -/
theorem iff_preservesColimitsOfShape (F : C ⥤ D) :
    PreservesFiniteNonemptyColimits F ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
        PreservesColimitsOfShape J F := sorry

/-- Preservation of finite nonempty colimits includes preservation of finite connected
colimits. -/
instance (priority := 90) preservesFiniteConnectedColimits
    (F : C ⥤ D) [PreservesFiniteNonemptyColimits F] :
    PreservesFiniteConnectedColimits F := sorry

namespace BinaryCoproducts

/-- Preservation of binary coproducts and finite connected colimits gives preservation of all
finite nonempty colimits. -/
theorem ofFiniteConnected
    (F : C ⥤ D) [HasFiniteNonemptyColimits C]
    [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [PreservesFiniteConnectedColimits F] :
    PreservesFiniteNonemptyColimits F := sorry

/-- For a functor whose source has finite nonempty colimits, preservation of those colimits is
equivalent to preservation of binary coproducts and finite connected colimits. -/
theorem iff_finiteConnected
    (F : C ⥤ D) [HasFiniteNonemptyColimits C] :
    PreservesFiniteNonemptyColimits F ↔
      PreservesColimitsOfShape (Discrete WalkingPair) F ∧
        PreservesFiniteConnectedColimits F := sorry

end BinaryCoproducts

/-- Preservation of finite nonempty colimits by `F` is preservation of finite nonempty limits by
the opposite functor. -/
theorem iff_limits_op (F : C ⥤ D) :
    PreservesFiniteNonemptyColimits F ↔
      PreservesFiniteNonemptyLimits F.op := sorry

/-- A functor preserving finite nonempty colimits induces an opposite functor preserving finite
nonempty limits. -/
theorem op (F : C ⥤ D) [PreservesFiniteNonemptyColimits F] :
    PreservesFiniteNonemptyLimits F.op := sorry

/-- A functor on opposite categories preserving finite nonempty colimits induces its unopposite
functor preserving finite nonempty limits. -/
theorem unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteNonemptyColimits F] :
    PreservesFiniteNonemptyLimits F.unop := sorry

end PreservesFiniteNonemptyColimits

namespace PreservesFiniteNonemptyLimits

/-- Preservation of finite nonempty limits by `F` is preservation of finite nonempty colimits by
the opposite functor. -/
theorem iff_colimits_op (F : C ⥤ D) :
    PreservesFiniteNonemptyLimits F ↔
      PreservesFiniteNonemptyColimits F.op := sorry

/-- A functor preserving finite nonempty limits induces an opposite functor preserving finite
nonempty colimits. -/
theorem op (F : C ⥤ D) [PreservesFiniteNonemptyLimits F] :
    PreservesFiniteNonemptyColimits F.op := sorry

/-- A functor on opposite categories preserving finite nonempty limits induces its unopposite
functor preserving finite nonempty colimits. -/
theorem unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteNonemptyLimits F] :
    PreservesFiniteNonemptyColimits F.unop := sorry

end PreservesFiniteNonemptyLimits

end CategoryTheory.Limits

