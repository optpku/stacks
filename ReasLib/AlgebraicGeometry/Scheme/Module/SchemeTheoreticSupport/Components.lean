/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.Noetherian.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension.GenericPoints
public import ReasLib.RingTheory.Module.Support.FiniteLength

/-!
# Components of the scheme-theoretic support of a coherent module

This file records finiteness and dimension properties of the irreducible components of the
scheme-theoretic support of a coherent module.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The images of the irreducible components of the scheme-theoretic support of a coherent
module on a scheme locally of finite type over a universally catenary base form a locally
finite family. -/
theorem locallyFinite_irreducibleComponents_moduleSupport
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (F : X.Modules) [F.IsCoherent] :
    LocallyFinite fun W : irreducibleComponents (schemeTheoreticSupport F).subscheme ↦
      (schemeTheoreticSupport F).subschemeι.base ''
        (W : Set (schemeTheoreticSupport F).subscheme) := sorry

/-- At a generic point of an irreducible component of the scheme-theoretic support of a
coherent module, its stalk has finite length over the ambient local ring. -/
theorem stalk_length_lt_top_at_genericPoint_moduleSupport
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (F : X.Modules) [F.IsCoherent]
    (ξ : genericPoints (schemeTheoreticSupport F).subscheme) :
    Module.length
      (X.presheaf.stalk ((schemeTheoreticSupport F).subschemeι ξ.1))
      (RingedSpace.stalkModuleCat F ((schemeTheoreticSupport F).subschemeι ξ.1)) < ⊤ := sorry

/-- A point of the scheme-theoretic support of a coherent module that attains an upper bound
for its `δ`-dimension is a generic point of an irreducible component. -/
theorem mem_genericPoints_moduleSupport_of_deltaDimension_le
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (F : X.Modules) [F.IsCoherent]
    (k : ℤ) (hdim : f.closedSubschemeDeltaDimension δ (schemeTheoreticSupport F) ≤ (k : EInt))
    (ξ : (schemeTheoreticSupport F).subscheme)
    (hξ : f.relativeDimensionFunction δ ((schemeTheoreticSupport F).subschemeι ξ) = k) :
    ξ ∈ genericPoints (schemeTheoreticSupport F).subscheme := sorry

end AlgebraicGeometry.Scheme.Modules
