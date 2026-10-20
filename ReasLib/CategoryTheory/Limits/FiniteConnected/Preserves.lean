module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preservation of finite connected limits and colimits

This leaf owns the universe-stable preservation classes and their pullback/equalizer and
pushout/coequalizer criteria. Category-level existence remains in `FiniteConnected.Basic`.
-/

@[expose] public section

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A functor preserves finite connected limits if it preserves limits of every finite connected
small diagram. -/
@[stacks 04AT "preservation of finite connected limits"]
class PreservesFiniteConnectedLimits (F : C ⥤ D) : Prop where
  /-- The functor preserves limits of every `Type`-small finite connected shape. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J] :
    PreservesLimitsOfShape J F

namespace PreservesFiniteConnectedLimits

/-- Preservation of finite connected limits supplies preservation for finite connected shapes in
every universe. -/
instance (priority := 90) preservesLimitsOfShape
    (F : C ⥤ D) [PreservesFiniteConnectedLimits F]
    (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J] :
    PreservesLimitsOfShape J F := sorry

/-- Preservation of all finite limits implies preservation of finite connected limits. -/
instance (priority := 100) ofFiniteLimits
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteConnectedLimits F := sorry

/-- A composite of functors preserving finite connected limits preserves them. -/
instance (priority := 40) comp
    (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteConnectedLimits F] [PreservesFiniteConnectedLimits G] :
    PreservesFiniteConnectedLimits (F ⋙ G) := sorry

/-- Preservation of finite connected limits transfers across a natural isomorphism. -/
theorem ofIso {F G : C ⥤ D} (e : F ≅ G) [PreservesFiniteConnectedLimits F] :
    PreservesFiniteConnectedLimits G := sorry

/-- Preservation of finite connected limits is invariant under natural isomorphism. -/
theorem iff_ofIso {F G : C ⥤ D} (e : F ≅ G) :
    PreservesFiniteConnectedLimits F ↔ PreservesFiniteConnectedLimits G := sorry

/-- Construct preservation of finite connected limits by supplying it in any one universe. -/
theorem ofSize
    (F : C ⥤ D)
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J],
      PreservesLimitsOfShape J F) :
    PreservesFiniteConnectedLimits F := sorry

/-- A functor preserves finite connected limits if and only if it preserves every finite connected
shape in any fixed universe. -/
theorem iff_preservesLimitsOfShape (F : C ⥤ D) :
    PreservesFiniteConnectedLimits F ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J],
        PreservesLimitsOfShape J F := sorry

namespace Pullbacks

/-- A functor preserving pullbacks and equalizers preserves every finite connected limit. -/
theorem ofEqualizers
    (F : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan F]
    [PreservesLimitsOfShape WalkingParallelPair F] :
    PreservesFiniteConnectedLimits F := sorry

/-- For a functor whose source has finite connected limits, preservation of those limits is
equivalent to preservation of pullbacks and equalizers. -/
@[stacks 04AT "finite connected limit preservation criteria"]
theorem iff_equalizers
    (F : C ⥤ D) [HasFiniteConnectedLimits C] :
    PreservesFiniteConnectedLimits F ↔
      PreservesLimitsOfShape WalkingCospan F ∧
        PreservesLimitsOfShape WalkingParallelPair F := sorry

end Pullbacks

end PreservesFiniteConnectedLimits

/-- A functor preserves finite connected colimits if it preserves colimits of every finite
connected small diagram. -/
@[stacks 04AV "preservation of finite connected colimits"]
class PreservesFiniteConnectedColimits (F : C ⥤ D) : Prop where
  /-- The functor preserves colimits of every `Type`-small finite connected shape. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J] :
    PreservesColimitsOfShape J F

namespace PreservesFiniteConnectedColimits

/-- Preservation of finite connected colimits supplies preservation for finite connected shapes
in every universe. -/
instance (priority := 90) preservesColimitsOfShape
    (F : C ⥤ D) [PreservesFiniteConnectedColimits F]
    (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J] :
    PreservesColimitsOfShape J F := sorry

/-- Preservation of all finite colimits implies preservation of finite connected colimits. -/
instance (priority := 100) ofFiniteColimits
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteConnectedColimits F := sorry

/-- A composite of functors preserving finite connected colimits preserves them. -/
instance (priority := 40) comp
    (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteConnectedColimits F] [PreservesFiniteConnectedColimits G] :
    PreservesFiniteConnectedColimits (F ⋙ G) := sorry

/-- Preservation of finite connected colimits transfers across a natural isomorphism. -/
theorem ofIso {F G : C ⥤ D} (e : F ≅ G) [PreservesFiniteConnectedColimits F] :
    PreservesFiniteConnectedColimits G := sorry

/-- Preservation of finite connected colimits is invariant under natural isomorphism. -/
theorem iff_ofIso {F G : C ⥤ D} (e : F ≅ G) :
    PreservesFiniteConnectedColimits F ↔ PreservesFiniteConnectedColimits G := sorry

/-- Construct preservation of finite connected colimits by supplying it in any one universe. -/
theorem ofSize
    (F : C ⥤ D)
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J],
      PreservesColimitsOfShape J F) :
    PreservesFiniteConnectedColimits F := sorry

/-- A functor preserves finite connected colimits if and only if it preserves every finite
connected shape in any fixed universe. -/
theorem iff_preservesColimitsOfShape (F : C ⥤ D) :
    PreservesFiniteConnectedColimits F ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J],
        PreservesColimitsOfShape J F := sorry

/-- Preservation of finite connected colimits by `F` is preservation of finite connected limits
by the opposite functor. -/
theorem iff_limits_op (F : C ⥤ D) :
    PreservesFiniteConnectedColimits F ↔
      PreservesFiniteConnectedLimits F.op := sorry

/-- A functor preserving finite connected colimits induces an opposite functor preserving finite
connected limits. -/
theorem op (F : C ⥤ D) [PreservesFiniteConnectedColimits F] :
    PreservesFiniteConnectedLimits F.op := sorry

/-- A functor on opposite categories preserving finite connected colimits induces its unopposite
functor preserving finite connected limits. -/
theorem unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteConnectedColimits F] :
    PreservesFiniteConnectedLimits F.unop := sorry

namespace Pushouts

/-- A functor preserving pushouts and coequalizers preserves every finite connected colimit. -/
theorem ofCoequalizers
    (F : C ⥤ D) [HasPushouts C] [HasCoequalizers C]
    [PreservesColimitsOfShape WalkingSpan F]
    [PreservesColimitsOfShape WalkingParallelPair F] :
    PreservesFiniteConnectedColimits F := sorry

/-- For a functor whose source has finite connected colimits, preservation of those colimits is
equivalent to preservation of pushouts and coequalizers. -/
@[stacks 04AV "finite connected colimit preservation criteria"]
theorem iff_coequalizers
    (F : C ⥤ D) [HasFiniteConnectedColimits C] :
    PreservesFiniteConnectedColimits F ↔
      PreservesColimitsOfShape WalkingSpan F ∧
        PreservesColimitsOfShape WalkingParallelPair F := sorry

end Pushouts

end PreservesFiniteConnectedColimits

namespace PreservesFiniteConnectedLimits

/-- Preservation of finite connected limits by `F` is preservation of finite connected colimits
by the opposite functor. -/
theorem iff_colimits_op (F : C ⥤ D) :
    PreservesFiniteConnectedLimits F ↔
      PreservesFiniteConnectedColimits F.op := sorry

/-- A functor preserving finite connected limits induces an opposite functor preserving finite
connected colimits. -/
theorem op (F : C ⥤ D) [PreservesFiniteConnectedLimits F] :
    PreservesFiniteConnectedColimits F.op := sorry

/-- A functor on opposite categories preserving finite connected limits induces its unopposite
functor preserving finite connected colimits. -/
theorem unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteConnectedLimits F] :
    PreservesFiniteConnectedColimits F.unop := sorry

end PreservesFiniteConnectedLimits

end CategoryTheory.Limits

