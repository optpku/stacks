module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge.Chain

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The curve dualizing module at a terminal rational-bridge contraction endpoint is ample. -/
theorem terminalContraction_curveDualizingModule_isAmple
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension h_global)
    {Y : SchemeOverField k} (chain : RationalBridge.ContractionChain X Y)
    (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y)) :
    Scheme.Modules.isAmpleObject
      (@curveDualizingModule k _ Y.left Y.hom chain.target_proper) := sorry

/-- Terminal rational-bridge contraction endpoints are independent of the chosen chain. -/
theorem stableContraction_independent
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension h_global)
    {Y₁ Y₂ : SchemeOverField k}
    (chain₁ : RationalBridge.ContractionChain X Y₁)
    (h₁ : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y₁))
    (chain₂ : RationalBridge.ContractionChain X Y₂)
    (h₂ : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y₂)) :
    ∃! e : Y₁ ≅ Y₂, chain₁.map ≫ e.hom = chain₂.map := sorry

/-- A field extension carries a terminal contraction morphism to a concrete contraction chain. -/
theorem stableContraction_existsBaseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension h_global)
    {Y : SchemeOverField k} (chain : RationalBridge.ContractionChain X Y)
    (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y)) :
    ∃ chainK : RationalBridge.ContractionChain
        (FieldExtension.Over.baseChange k K X)
        (FieldExtension.Over.baseChange k K Y),
      chainK.map = (FieldExtension.Over.functor k K).map chain.map := sorry

/-- A terminal contraction endpoint remains free of rational bridges after a field extension. -/
theorem stableContraction_baseChangeNoBridge
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension h_global)
    {Y : SchemeOverField k} (chain : RationalBridge.ContractionChain X Y)
    (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y)) :
    ¬ Nonempty
      (AlgebraicGeometry.RationalBridge (FieldExtension.Over.baseChange k K Y)) := sorry

/-- Terminal contraction chains after a field extension have a unique compatible endpoint isomorphism. -/
theorem stableContraction_commutesWithBaseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension h_global)
    {Y : SchemeOverField k} (chain : RationalBridge.ContractionChain X Y)
    (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y))
    {YK : SchemeOverField K}
    (chainK : RationalBridge.ContractionChain
      (FieldExtension.Over.baseChange k K X) YK)
    (h_no_bridgeK : ¬ Nonempty (AlgebraicGeometry.RationalBridge YK)) :
    ∃! e : FieldExtension.Over.baseChange k K Y ≅ YK,
      (FieldExtension.Over.functor k K).map chain.map ≫ e.hom = chainK.map := sorry

end AlgebraicGeometry.SchemeOverField
