/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Support
public import ReasLib.AlgebraicGeometry.Scheme.K0.CoherentSupport
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.CategoryTheory.Pretriangulated.K0.Universal

/-!
# Euler classes of perfect complexes with support

This file defines the supported coherent Euler class of a perfect complex whose cohomology
is set-theoretically supported on a prescribed subset, together with the induced homomorphism
between the corresponding Grothendieck groups.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0WithSupport

private theorem moduleSupport_coproduct_subset
    {Y : RingedSpace.{u}} {ι : Type} (F : ι → Y.Modules) (T : Set Y)
    (hF : ∀ i, RingedSpace.moduleSupport (F i) ⊆ T) :
    RingedSpace.moduleSupport (∐ F) ⊆ T := by
  intro x hx
  by_contra h
  let G := RingedSpace.stalkModuleFunctor (X := Y) x
  letI : PreservesColimits G :=
    RingedSpace.stalkModuleFunctor_preservesColimits (X := Y) x
  letI : PreservesColimitsOfSize.{0, 0} G := preservesColimitsOfSize_shrink G
  have hFzero (i : ι) : IsZero (G.obj (F i)) := by
    have hzero : IsZero (TopCat.Presheaf.stalk (F i).val.presheaf x) := by
      by_contra hn
      exact h (hF i hn)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (AddCommGrpCat.isZero_iff_subsingleton.mp hzero)
  have hz : IsZero (G.obj (∐ F)) :=
    (isColimitOfPreserves G (colimit.isColimit (Discrete.functor F))).isZero_pt
      ((Discrete.functor F ⋙ G).isZero (fun i ↦ hFzero i.as))
  exact hx (AddCommGrpCat.isZero_iff_subsingleton.mpr
    (ModuleCat.isZero_iff_subsingleton.mp hz))

variable (X : Scheme.{u}) [IsLocallyNoetherian X] (T : Set X)

/-- The coproduct of the even cohomology sheaves of a supported perfect complex is
coherent. -/
theorem evenCohomology_isCoherent
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    (∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf E.obj (2 * i)).IsCoherent :=
  sorry

/-- The coproduct of the even cohomology sheaves of a supported perfect complex remains
supported on `T`. -/
theorem evenCohomology_support_subset
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    RingedSpace.moduleSupport
      (∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf E.obj (2 * i)) ⊆ T :=
  moduleSupport_coproduct_subset _ T (fun i ↦ E.property.2 (2 * i))

/-- The supported coherent sheaf given by the coproduct of the even cohomology sheaves. -/
noncomputable def evenCohomology
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    RingedSpace.CohSupportedOn X.toRingedSpace T :=
  ⟨⟨∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf E.obj (2 * i),
      evenCohomology_isCoherent X T E⟩,
    (RingedSpace.Coh.supportedOn_iff T _).2
      (evenCohomology_support_subset X T E)⟩

/-- The underlying module of `evenCohomology` is the even cohomology coproduct. -/
theorem evenCohomology_obj
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    (evenCohomology X T E).obj.obj =
      ∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf E.obj (2 * i) :=
  rfl

/-- The coproduct of the odd cohomology sheaves of a supported perfect complex is
coherent. -/
theorem oddCohomology_isCoherent
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    (∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf E.obj (2 * i + 1)).IsCoherent :=
  sorry

/-- The coproduct of the odd cohomology sheaves of a supported perfect complex remains
supported on `T`. -/
theorem oddCohomology_support_subset
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    RingedSpace.moduleSupport
      (∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf E.obj (2 * i + 1)) ⊆ T :=
  moduleSupport_coproduct_subset _ T (fun i ↦ E.property.2 (2 * i + 1))

/-- The supported coherent sheaf given by the coproduct of the odd cohomology sheaves. -/
noncomputable def oddCohomology
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    RingedSpace.CohSupportedOn X.toRingedSpace T :=
  ⟨⟨∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf E.obj (2 * i + 1),
      oddCohomology_isCoherent X T E⟩,
    (RingedSpace.Coh.supportedOn_iff T _).2
      (oddCohomology_support_subset X T E)⟩

/-- The underlying module of `oddCohomology` is the odd cohomology coproduct. -/
theorem oddCohomology_obj
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    (oddCohomology X T E).obj.obj =
      ∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf E.obj (2 * i + 1) :=
  rfl

/-- The supported coherent Euler class of a supported perfect complex. -/
noncomputable def eulerValue
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) : K0'WithSupport X T :=
  K0'WithSupport.of X T (evenCohomology X T E) -
    K0'WithSupport.of X T (oddCohomology X T E)

/-- The supported Euler class is the even cohomology class minus the odd cohomology class. -/
theorem eulerValue_def
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    eulerValue X T E =
      K0'WithSupport.of X T (evenCohomology X T E) -
        K0'WithSupport.of X T (oddCohomology X T E) :=
  rfl

/-- Supported coherent Euler classes are additive on distinguished triangles. -/
theorem eulerValue_distinguished
    (S : Triangle (RingedSpace.ModuleDerived.PerfectSupportedOn T))
    (hS : S ∈ distTriang
      (RingedSpace.ModuleDerived.PerfectSupportedOn T)) :
    eulerValue X T S.obj₂ = eulerValue X T S.obj₁ + eulerValue X T S.obj₃ :=
  sorry

/-- The Euler homomorphism from supported perfect `K₀` to supported coherent `K₀`. -/
noncomputable def toCoherent : K0WithSupport X T →+ K0'WithSupport X T :=
  TriangulatedK0.liftOfDistinguished (eulerValue X T)
    (eulerValue_distinguished X T)

/-- The supported Euler homomorphism sends a perfect generator to its Euler class. -/
theorem toCoherent_of
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    toCoherent X T (TriangulatedK0.of E) = eulerValue X T E := by
  change FreeAbelianGroup.lift (eulerValue X T) (FreeAbelianGroup.of E) =
    eulerValue X T E
  exact FreeAbelianGroup.lift_apply_of _ _

/-- For a closed immersion into a locally Noetherian scheme, the supported Euler
homomorphism sends a perfect generator to the difference of its even and odd cohomology
coproduct classes. -/
theorem toCoherent_of_closedImmersion {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    toCoherent X (Set.range i.base) (TriangulatedK0.of E) =
      K0'WithSupport.of X (Set.range i.base)
          (evenCohomology X (Set.range i.base) E) -
        K0'WithSupport.of X (Set.range i.base)
          (oddCohomology X (Set.range i.base) E) :=
  (toCoherent_of X (Set.range i.base) E).trans
    (eulerValue_def X (Set.range i.base) E)

end AlgebraicGeometry.Scheme.K0WithSupport
