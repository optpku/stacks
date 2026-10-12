/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap54.Lemma_54_2_4_Trace
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.PurelyInseparableTrace

/-- The generic-stalk trace selected by its presentation-independent characterization. -/
noncomputable def genericTrace
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i) :
    RingedSpace.stalkModuleCat (sourceModule p S X Y f i) (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
        (genericPoint X.left) :=
  Classical.epsilon fun τ ↦
    isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i τ

/-- The selected generic trace satisfies the presentation-independent characterization of
Lemma 54.2.2. -/
theorem genericTrace_spec
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i) :
    isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i
      (genericTrace hX hY h_pi h_degree h_i) := sorry

/-- The presentation-independent characterization uniquely determines the selected generic
trace. -/
theorem genericTrace_unique
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i)
    {τ : RingedSpace.stalkModuleCat (sourceModule p S X Y f i) (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
        (genericPoint X.left)}
    (hτ : isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i τ) :
    τ = genericTrace hX hY h_pi h_degree h_i := sorry

/-- The scheme-level morphism obtained by inverting the generic-stalk map on the prescribed
reflexive-hull extension. This construction does not consume a proof-level existence witness. -/
noncomputable def constructedTraceMap
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])] :
    sourceModule p S X Y f i ⟶ targetModule p S X i :=
  Function.invFun
    (fun φ : sourceModule p S X Y f i ⟶ targetModule p S X i ↦
      RingedSpace.moduleStalkHom (genericPoint X.left) φ)
    (genericTrace hX hY h_pi h_degree h_i ≫
      RingedSpace.moduleStalkHom (genericPoint X.left)
        (Scheme.Modules.toReflexiveHull
          ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)))

/-- The constructed scheme-level trace has the prescribed generic-stalk extension property. -/
theorem constructedTraceMap_spec
    {p : ℕ} [Fact p.Prime]
    {S : SchemeOverField (ZMod p)} {X Y : Over S.left}
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    {f : Y ⟶ X} [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    {i : ℕ} (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])] :
    RingedSpace.moduleStalkHom (genericPoint X.left)
        (constructedTraceMap hX hY h_pi h_degree h_i) =
      genericTrace hX hY h_pi h_degree h_i ≫
        RingedSpace.moduleStalkHom (genericPoint X.left)
          (Scheme.Modules.toReflexiveHull
            ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)) := sorry

/-- The generic-stalk trace characterized by Lemma 54.2.2 is independent of the auxiliary
presentation data used to describe it. -/
theorem isHigherTraceAtGenericPoint_unique
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p))
    (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    {τ₁ τ₂ : RingedSpace.stalkModuleCat (sourceModule p S X Y f i)
      (genericPoint X.left) ⟶
      RingedSpace.stalkModuleCat ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)
        (genericPoint X.left)}
    (hτ₁ : isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i τ₁)
    (hτ₂ : isHigherTraceAtGenericPoint S X Y f hX hY h_pi h_degree i h_i τ₂) :
    τ₁ = τ₂ := sorry

/-- The canonical trace-map specification is the fixed generic-stalk reflexive-hull equation. -/
def canonicalTraceMapSpec
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])]
    (φ : sourceModule p S X Y f i ⟶ targetModule p S X i) : Prop :=
    RingedSpace.moduleStalkHom (genericPoint X.left) φ =
      genericTrace hX hY h_pi h_degree h_i ≫
        RingedSpace.moduleStalkHom (genericPoint X.left)
          (Scheme.Modules.toReflexiveHull
            ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules))

/-- The canonical trace-map specification unfolds to the generic-stalk extension equation. -/
theorem canonicalTraceMapSpec_iff
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p)) (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])]
    (φ : sourceModule p S X Y f i ⟶ targetModule p S X i) :
    canonicalTraceMapSpec p S X Y f hX hY h_pi h_degree i h_i φ ↔
      RingedSpace.moduleStalkHom (genericPoint X.left) φ =
        genericTrace hX hY h_pi h_degree h_i ≫
          RingedSpace.moduleStalkHom (genericPoint X.left)
            (Scheme.Modules.toReflexiveHull
              ((Λ[i] Ω[X.hom.toShHom]) : X.left.Modules)) := sorry

/-- Lemma 54.2.4: for a finite dominant purely inseparable morphism of degree `p` between
Noetherian normal integral schemes over an `F_p`-scheme, the canonical generic-stalk trace extends
to a morphism from `f_* Λ[i] Ω[Y/S]` to the reflexive hull of `Λ[i] Ω[X/S]` for `i ≥ 1`. -/
@[stacks 0AX6]
noncomputable def traceMap
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p))
    (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])] :
    sourceModule p S X Y f i ⟶ targetModule p S X i :=
  constructedTraceMap hX hY h_pi h_degree h_i

/-- The generic stalk of `traceMap` recovers the canonical higher trace of Lemma 54.2.2. -/
theorem traceMap_spec
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p))
    (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])] :
    canonicalTraceMapSpec p S X Y f hX hY h_pi h_degree i h_i
      (traceMap p S X Y f hX hY h_pi h_degree i h_i) := sorry

/-- The canonical generic-stalk specification uniquely determines `traceMap`. -/
theorem traceMap_unique
    (p : ℕ) [Fact p.Prime]
    (S : SchemeOverField (ZMod p))
    (X Y : Over S.left)
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    (f : Y ⟶ X) [IsFinite f.left] [IsDominant f.left]
    (hX : X.left.isNormal) (hY : Y.left.isNormal)
    (h_pi : (f.left.functionFieldMap
      f.left.map_genericPoint_eq_of_isDominant).IsPurelyInseparable)
    (h_degree : f.left.inducedFunctionFieldDegree = p)
    (i : ℕ) (h_i : 1 ≤ i)
    [SheafOfModules.IsCoherent (Ω[X.hom.toShHom])]
    {φ : sourceModule p S X Y f i ⟶ targetModule p S X i}
    (hφ : canonicalTraceMapSpec p S X Y f hX hY h_pi h_degree i h_i φ) :
    φ = traceMap p S X Y f hX hY h_pi h_degree i h_i := sorry

end AlgebraicGeometry.Scheme.PurelyInseparableTrace

end
