/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.Ext
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Noetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory DerivedCategory.TStructure
open CategoryTheory.MonoidalClosed
open RingedSpace.Module.Derived RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace ProjectionFormula

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [hS_noetherian : IsNoetherian S] [hf_finiteType : LocallyOfFiniteType f]
variable (E : DerivedCategory.CohomologyIn
  (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
variable (hE_boundedAbove :
  (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj)
variable (hE_coherent : DerivedCategory.cohomologyIn
  (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E.obj)
variable (G : CochainComplex X.Modules ℤ)
variable (hG_bounded : CochainComplex.bounded X.Modules G)
variable [hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent]
variable [∀ i : ℤ, SheafOfModules.IsFlatOver (G.X i) f.toShHom]
variable [hG_properSupport : ∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
  (RingedSpace.ModuleDerived.cohomologySheaf (DerivedCategory.Q.obj G) i)]
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [KFlat.TensorDescends S.toRingedSpace]
variable [KFlat.IsLocalization S.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]

include hS_noetherian hf_finiteType hE_boundedAbove hE_coherent hG_bounded
  hG_coherent hG_properSupport

/-- Through every degree `m`, Ext against a bounded-above object with coherent
cohomology is naturally approximated by tensoring with a perfect object,
compatibly with connecting maps. -/
theorem existsPerfectExtApproximation (m : ℤ) :
    ∃ (K : RingedSpace.ModuleDerived S.toRingedSpace)
      (hK : RingedSpace.ModuleDerived.IsPerfect K)
      (α : CohomologyTransform (extDelta f E.obj G) (tensorDelta S K)),
      ∀ i : ℤ, i ≤ m → IsIso (α.app i) := sorry

/-- Ext against a bounded-above object with coherent cohomology is naturally
represented in every degree by a pseudo-coherent object, compatibly with
connecting maps. -/
theorem existsPseudoCoherentExtRepresentation :
    ∃ (L : RingedSpace.ModuleDerived S.toRingedSpace)
      (hL : RingedSpace.ModuleDerived.IsPseudoCoherent L)
      (α : CohomologyTransform (representedExtDelta S L) (extDelta f E.obj G)),
      ∀ i : ℤ, IsIso (α.app i) := sorry

end ProjectionFormula
end ModuleDerived
end Scheme
end AlgebraicGeometry
