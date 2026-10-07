module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Ext.FiniteTotalDimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded
open scoped DerivedExt DerivedCategory.CohomologyIn

universe u

/- Lemma 57.5.3: for a proper scheme over a field, a bounded coherent complex `K`
and a perfect derived module `E`, the graded family of derived Ext modules has
finite total dimension over the field. -/
@[stacks 0FYC] #check
  (AlgebraicGeometry.Scheme.Hom.DerivedExt.finiteTotalDimension_of_isPerfect :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (K : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E),
      GradedObject.FiniteTotalDimension
        (fun i : ℤ ↦ AlgebraicGeometry.Scheme.Hom.DerivedExt.value f E
          (ι.obj K.obj) i))
