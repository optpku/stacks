/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.WithBotTop
public import Mathlib.Topology.LocallyFinsupp
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap69.Lemma_69_12_7_Coherent
public import stacks_project.Chap72.Lemma_72_6_1
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Lemma_82_4_1_Length
public import stacks_project.Chap82.Lemma_82_4_3_Length
public import stacks_project.Chap82.Lemma_82_4_4_GenericPoint

/-!
# Associated cycles of coherent modules on algebraic spaces

This file defines the length of a module at a point of `|X|`, the multiplicity of an
irreducible component of the support of a coherent `𝒪_X`-module, and the
multiplicity-weighted `k`-cycle associated to that module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The length of an `𝒪_X`-module at a point of `|X|` is the supremum of étale-stalk
lengths at geometric points over that point. -/
noncomputable def lengthAt (F : X.Modules) (x : Points X) : ℕ∞ :=
  ⨆ p : {p : GeometricPoint X // p.liesOver x}, lengthAtGeometricPoint F p.1

/-- Unfolding of `lengthAt` as a supremum of `lengthAtGeometricPoint`. -/
theorem lengthAt_eq (F : X.Modules) (x : Points X) :
    lengthAt F x =
      ⨆ p : {p : GeometricPoint X // p.liesOver x}, lengthAtGeometricPoint F p.1 :=
  sorry

/-- For a coherent module on a locally Noetherian algebraic space, the length at a point
agrees with the étale-stalk length at any geometric point over it. -/
theorem lengthAt_eq_lengthAtGeometricPoint [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (xbar : GeometricPoint X) (hx : xbar.liesOver x) :
    lengthAt F x = lengthAtGeometricPoint F xbar :=
  sorry

/-- The numeric `lengthAt` payload witnesses `hasLengthAt`. -/
theorem hasLengthAt_lengthAt [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : Points X) :
    hasLengthAt F x (lengthAt F x) :=
  sorry

/-- The support of a coherent `𝒪_X`-module on a locally Noetherian algebraic space is
closed in `|X|`. -/
theorem isClosed_moduleSupport_of_isCoherent [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] : IsClosed (moduleSupport F) :=
  sorry

/-- The multiplicity of an irreducible component of `moduleSupport F` is the length of
`F` at the generic point of that component. -/
noncomputable def componentMultiplicity [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (hx : IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)) : ℕ :=
  (lengthAt F x).toNat

/-- The component multiplicity is the finite value of `lengthAt` at the generic point. -/
theorem componentMultiplicity_eq_lengthAt [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (hx : IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)) :
    (componentMultiplicity F x hx : ℕ∞) = lengthAt F x :=
  sorry

/-- The component multiplicity witnesses `hasLengthAt` at the generic point. -/
theorem hasLengthAt_componentMultiplicity [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (hx : IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)) :
    hasLengthAt F x (componentMultiplicity F x hx) :=
  sorry

/-- The multiplicity of an irreducible component of the support of a coherent module is a
positive integer. -/
theorem componentMultiplicity_pos [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (hx : IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)) :
    0 < componentMultiplicity F x hx :=
  sorry

/-- The multiplicity-weighted coefficient function of a coherent module, restricted to its
dimension-`k` support generic points, has locally finite support. -/
theorem associatedCycle_locallyFiniteSupport [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (d : Points X → ℤ) (k : ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      @ite ℤ (IsGenericPoint.ofIrreducibleComponent x (moduleSupport F) ∧ d x = k)
        (Classical.propDecidable _) ((lengthAt F x).toNat : ℤ) 0 :=
  sorry

/-- The multiplicity-weighted degree-`k` cycle associated to a coherent `𝒪_X`-module. -/
noncomputable def associatedCycle [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (d : Points X → ℤ) (k : ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦
    @ite ℤ (IsGenericPoint.ofIrreducibleComponent x (moduleSupport F) ∧ d x = k)
      (Classical.propDecidable _) ((lengthAt F x).toNat : ℤ) 0
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    associatedCycle_locallyFiniteSupport F d k x

/-- Coefficients of the associated cycle are the length at a dimension-`k` generic point of
the support, and vanish otherwise. -/
theorem associatedCycle_apply [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (d : Points X → ℤ) (k : ℤ) (x : Points X) :
    associatedCycle F d k x =
      @ite ℤ (IsGenericPoint.ofIrreducibleComponent x (moduleSupport F) ∧ d x = k)
        (Classical.propDecidable _) ((lengthAt F x).toNat : ℤ) 0 :=
  sorry

/-- Off the dimension-`k` locus, the associated cycle coefficient vanishes. -/
theorem associatedCycle_eq_zero_of_dimension_ne [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (d : Points X → ℤ) (k : ℤ) {x : Points X}
    (hx : d x ≠ k) : associatedCycle F d k x = 0 :=
  sorry

end Modules

namespace Hom

/-- The `δ`-dimension of the support of a coherent `𝒪_X`-module. -/
noncomputable def moduleSupportDeltaDimension {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] : EInt :=
  (closedSetDeltaDimension f) δ
    ⟨Modules.moduleSupport F,
      @Modules.isClosed_moduleSupport_of_isCoherent S X
        (LocallyOfFiniteType.isLocallyNoetherian f) F _⟩

/-- Unfolding of `moduleSupportDeltaDimension` as `closedSetDeltaDimension` of the
support. -/
theorem moduleSupportDeltaDimension_def {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] :
    (moduleSupportDeltaDimension f) δ F =
      (closedSetDeltaDimension f) δ
        ⟨Modules.moduleSupport F,
          @Modules.isClosed_moduleSupport_of_isCoherent S X
            (LocallyOfFiniteType.isLocallyNoetherian f) F _⟩ :=
  sorry

/-- The degree-`k` cycle associated to a coherent `𝒪_X`-module, measured using the
relative dimension function of a good morphism. -/
noncomputable def moduleCycle {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : (moduleSupportDeltaDimension f) δ F ≤ (k : EInt)) :
    Function.locallyFinsupp (Points X) ℤ :=
  @Modules.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) F _
    ((relativeDimensionFunction f) δ) k

/-- The module cycle is the associated cycle for the relative dimension function. -/
theorem moduleCycle_eq_associatedCycle {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : (moduleSupportDeltaDimension f) δ F ≤ (k : EInt)) :
    moduleCycle f δ F k hF =
      @Modules.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) F _
        ((relativeDimensionFunction f) δ) k :=
  sorry

/-- Coefficients of the module cycle are the length at a `δ`-dimension-`k` generic point of
the support, and vanish otherwise. -/
theorem moduleCycle_apply {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hF : (moduleSupportDeltaDimension f) δ F ≤ (k : EInt)) (x : Points X) :
    moduleCycle f δ F k hF x =
      @ite ℤ
        (IsGenericPoint.ofIrreducibleComponent x (Modules.moduleSupport F) ∧
          (relativeDimensionFunction f) δ x = k)
        (Classical.propDecidable _) ((Modules.lengthAt F x).toNat : ℤ) 0 :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
