/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail.Chain
public import ReasLib.AlgebraicGeometry.Scheme.OverField.DualizingSemiampleness
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry
namespace SchemeOverField
namespace RationalTail
namespace ContractionChain

/-- A terminating rational-tail contraction chain in genus zero has
endpoint an irreducible plane conic. -/
theorem endpointPlaneConic
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : genus X h_dimension h_global = 0) :
    ∃ (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
      (F : MvPolynomial (Fin 3) k),
      IsIntegral Z.subscheme ∧
        Nonempty (Y ≅ Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)) ∧
        HasHomogeneousEquation 2 Z F ∧ F.totalDegree = 2 := sorry

/-- The dualizing module of the endpoint of a rational-tail contraction chain. -/
noncomputable def endpointDualizingModule
    {k : Type u} [Field k] {X Y : SchemeOverField k} [IsProper X.hom]
    (chain : ContractionChain X Y) : Y.left.Modules :=
  @dualizingModule k _ Y.left Y.hom chain.targetProper

/-- A terminating rational-tail contraction chain in genus one has
trivial dualizing module on its endpoint. -/
theorem endpointDualizingIso
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : genus X h_dimension h_global = 1) :
    Nonempty
      (endpointDualizingModule chain ≅
        (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules)) := sorry

/-- The endpoint dualizing module of a rational-tail contraction chain is invertible. -/
theorem endpointDualizingInvertible
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) :
    Scheme.Modules.Invertible
      (endpointDualizingModule chain) := sorry

/-- The integral tensor power of the endpoint dualizing module of a proper nodal curve. -/
noncomputable def endpointDualizingPower
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (m : ℤ) : Y.left.Modules :=
  @Scheme.Modules.tensorPowerInt Y.left (endpointDualizingModule chain)
    (endpointDualizingInvertible X h_dimension h_global h_nodal chain) m

/-- In genus at least two, every integral tensor power of the endpoint
dualizing module of exponent at least two is globally generated. -/
theorem endpointTensorPowerGloballyGenerated
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension h_global)
    (m : ℤ) (h_m : (2 : ℤ) ≤ m) :
    SheafOfModules.IsGloballyGenerated
      (endpointDualizingPower X h_dimension h_global h_nodal chain m) := sorry

/-- in positive genus, any two terminal rational-tail contraction chains
have uniquely compatibly isomorphic endpoints. -/
theorem uniqueEndpoint
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y Z : SchemeOverField k}
    (chainY : ContractionChain X Y) (h_Y : ¬ Nonempty (RationalTail Y))
    (chainZ : ContractionChain X Z) (h_Z : ¬ Nonempty (RationalTail Z))
    (h_genus : (1 : ℕ) ≤ genus X h_dimension h_global) :
    ∃! e : Y ≅ Z, chainY.map ≫ e.hom = chainZ.map := sorry

/-- After a field extension, the base-changed contraction morphism is
represented by a concrete rational-tail contraction chain. -/
theorem existsBaseChange
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : (1 : ℕ) ≤ genus X h_dimension h_global)
    (K : Type u) [Field K] [Algebra k K] :
    ∃ chainK : ContractionChain (FieldExtension.Over.baseChange k K X)
        (FieldExtension.Over.baseChange k K Y),
      chainK.map = (FieldExtension.Over.functor k K).map chain.map := sorry

/-- Rational tails do not reappear on the endpoint after extending the
ground field. -/
theorem baseChangeNoTail
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : (1 : ℕ) ≤ genus X h_dimension h_global)
    (K : Type u) [Field K] [Algebra k K] :
    ¬ Nonempty (RationalTail (FieldExtension.Over.baseChange k K Y)) := sorry

/-- Every terminal base-changed contraction chain has a unique endpoint
isomorphism compatible with the base-changed original contraction morphism. -/
theorem commutesWithBaseChange
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) {Y : SchemeOverField k}
    (chain : ContractionChain X Y) (h_no_tail : ¬ Nonempty (RationalTail Y))
    (h_genus : (1 : ℕ) ≤ genus X h_dimension h_global)
    (K : Type u) [Field K] [Algebra k K] {Z : SchemeOverField K}
    (chainK : ContractionChain (FieldExtension.Over.baseChange k K X) Z)
    (h_Z : ¬ Nonempty (RationalTail Z)) :
    ∃! e : FieldExtension.Over.baseChange k K Y ≅ Z,
      (FieldExtension.Over.functor k K).map chain.map ≫ e.hom = chainK.map := sorry

end ContractionChain
end RationalTail
end SchemeOverField
end AlgebraicGeometry
