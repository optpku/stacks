/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Cohomology.RHomExt

/-!
# The common proper stage of compact-support restriction duality

For a map of coherent ideal stages I' → I, ordinary restriction is
precomposition in RHom and compact restriction is tensoring that same map.
The horizontal arrows are the specified normalized proper pairings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat Scheme.Hom DerivedCategory.TStructure
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.Cohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable {I I' : Scheme.DerivedQCoh X} (a : I' ⟶ I) (M : Scheme.DerivedQCoh X)
variable (hI : DerivedCategory.cohomologyIn (SheafOfModules.isCoherent X.ringCatSheaf) I.obj)
variable (hIa : (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) I.obj)
variable (hI' : DerivedCategory.cohomologyIn (SheafOfModules.isCoherent X.ringCatSheaf) I'.obj)
variable (hI'a : (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) I'.obj)
variable (hM : DerivedCategory.cohomologyIn (SheafOfModules.isCoherent X.ringCatSheaf) M.obj)
variable (hMb : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) M.obj)

/-- Precomposition by the actual map I' → I gives the ordinary stage map
RHom(I,M) → RHom(I',M). -/
def ordinaryStageMap :
    ordinaryStage I M hI hIa hM hMb ⟶ ordinaryStage I' M hI' hI'a hM hMb :=
  ObjectProperty.homMk
    ((MonoidalClosed.pre ((Scheme.DerivedQCoh.inclusion X).map a)).app M.obj)

/-- The ordinary degree-n restriction map is proper cohomology applied to
the specified RHom precomposition map. -/
def ordinaryStageCohomologyMap (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q] (n : ℤ) :=
  cohomologyOverFieldMap q (ordinaryStageMap a M hI hIa hI' hI'a hM hMb) n

/-- The compact tensor-stage map is homology of the actual map
RHom(M,q!O) ⊗ I' → RHom(M,q!O) ⊗ I. -/
def compactTensorStageMap (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q] (n : ℤ) :=
  (globalCohomologyOverField q n).map
    (𝟙 ((ihom M.obj).obj (Scheme.DerivedQCoh.properDualizingComplex q).obj) ⊗ₘ
      (Scheme.DerivedQCoh.inclusion X).map a)

/-- The proper stage square is natural in the ideal stage. Its two vertical
maps come from the same a, and its horizontal maps are constructed above;
there is no compatibility or stage-square premise. -/
theorem properTensorStagePairing_naturality
    (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q] (n : ℤ) :
    (properTensorStagePairing q I M hI hIa hM hMb n).comp
        (compactTensorStageMap a M q n).hom =
      (ordinaryStageCohomologyMap a M hI hIa hI' hI'a hM hMb q (-n)).hom.dualMap.comp
        (properTensorStagePairing q I' M hI' hI'a hM hMb n) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.Cohomology
