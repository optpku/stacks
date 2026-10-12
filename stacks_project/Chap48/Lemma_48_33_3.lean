/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.DegreeZero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn
open RingedSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

/- Lemma 48.33.3 -/
@[stacks 0G5C] #check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.range_degreeZeroRestrictionMap :
  ∀ {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    [IsProper (Over.hom X.obj)]
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (h_negative : ∀ q < 0,
      IsZero (cohomologySheaf
        ((ambient (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K) q))
    (Z : TopologicalSpace.Closeds (Over.left X.obj : Scheme))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (h_ideal : I.openComplement = Z.compl),
    Set.range (degreeZeroRestrictionMap X I K) =
      {s | ∃ V : TopologicalSpace.Opens (Over.left X.obj : Scheme),
        (Z : Set (Over.left X.obj : Scheme)) ⊆ (V : Set (Over.left X.obj : Scheme)) ∧
          (RingedSpace.sectionFromTop
            (cohomologySheaf
              ((ambient (SheafOfModules.isCoherent
              (Over.left X.obj).ringCatSheaf)).obj K) 0) s).1
          (Opposite.op V) = 0})

#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.degreeZeroRestrictionMap_injective :
  ∀ {k : Type u} [Field k]
    (X : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    [IsProper (Over.hom X.obj)]
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf])
    (h_negative : ∀ q < 0,
      IsZero (cohomologySheaf
        ((ambient (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).obj K) q))
    (Z : TopologicalSpace.Closeds (Over.left X.obj : Scheme))
    (I : (Over.left X.obj : Scheme).IdealSheafData)
    (h_ideal : I.openComplement = Z.compl),
    Function.Injective (degreeZeroRestrictionMap X I K))

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
