/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration.Small
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

/-!
# Smallness of cardinal-generated quasi-coherent modules

Cardinal-generated quasi-coherent modules on a scheme form an essentially small
object property relative to the universe of the scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- Cardinal-generated quasi-coherent modules on a scheme `X : Scheme.{u}` form an object
property that is essentially small relative to the universe `u` of `X`. -/
instance isKappaGenerated_essentiallySmall (X : Scheme.{u}) (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u}
      (fun E : X.QCoh => E.obj.IsKappaGenerated κ) := by
  let P : ObjectProperty X.QCoh := fun E => E.obj.IsKappaGenerated κ
  have h_map : ObjectProperty.EssentiallySmall.{u} (P.map (inclusion X)) := by
    exact @ObjectProperty.EssentiallySmall.of_le.{u, u, u + 1}
      X.Modules inferInstance (P.map (inclusion X))
      (fun M : X.Modules => M.IsKappaGenerated κ)
      (SheafOfModules.IsKappaGenerated.essentiallySmall (R := X.ringCatSheaf) κ)
      (by
        rintro M ⟨E, hE, ⟨e⟩⟩
        exact (SheafOfModules.isKappaGenerated_iff_of_iso e κ).mp hE)
  have h_fiber : ∀ M : X.Modules,
      ObjectProperty.EssentiallySmall.{u}
        (P ⊓ fun E => Nonempty ((inclusion X).obj E ≅ M)) := by
    intro M
    by_cases hM : ∃ E : X.QCoh,
        E.obj.IsKappaGenerated κ ∧ Nonempty ((inclusion X).obj E ≅ M)
    · obtain ⟨E, hE, ⟨e⟩⟩ := hM
      refine ⟨ObjectProperty.ofObj (fun _ : Unit => E), inferInstance, ?_⟩
      rintro E' ⟨hE', ⟨e'⟩⟩
      refine ⟨E, ⟨()⟩, ⟨?_⟩⟩
      exact (inclusion X).preimageIso (e' ≪≫ e.symm)
    · have hsmall : ObjectProperty.Small.{u} (⊥ : ObjectProperty X.QCoh) := by
        let f : Subtype (⊥ : ObjectProperty X.QCoh) → PEmpty.{u + 1} :=
          fun x ↦ x.property.elim
        exact small_of_injective (α := Subtype (⊥ : ObjectProperty X.QCoh))
          (β := PEmpty.{u + 1}) (f := f) (by
            intro x y _
            exact x.property.elim)
      refine ⟨⊥, hsmall, ?_⟩
      rintro E ⟨hE, he⟩
      exact (hM ⟨E, hE, he⟩).elim
  exact ObjectProperty.EssentiallySmall.of_functor P (inclusion X) h_map h_fiber

end AlgebraicGeometry.Scheme.QCoh
