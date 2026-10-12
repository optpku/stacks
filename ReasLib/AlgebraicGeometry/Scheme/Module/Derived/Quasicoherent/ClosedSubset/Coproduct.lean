/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.coreflector

/-- The coreflector onto quasicoherent complexes supported on a closed subset with
retrocompact complement preserves coproducts indexed in the ambient universe. -/
instance preservesCoproducts (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
    (hT : IsRetrocompact ((T : Set X)ᶜ)) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (SupportedOn.coreflector X T hT) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.coreflector

namespace AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn

/-- The derived category of quasi-coherent modules supported on a closed subset admits
arbitrary coproducts indexed in the ambient universe. -/
instance hasCoproducts (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    HasCoproducts.{u} (SupportedOn X T) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn
