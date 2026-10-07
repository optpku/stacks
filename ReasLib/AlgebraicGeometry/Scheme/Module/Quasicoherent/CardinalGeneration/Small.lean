module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration.Small
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

/-!
# Smallness of cardinal-generated quasi-coherent modules

Cardinal-generated quasi-coherent modules on a scheme form an essentially small
object property.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- Cardinal-generated quasi-coherent modules on a scheme form an essentially small
object property. -/
instance isKappaGenerated_essentiallySmall (X : Scheme.{u}) (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u + 1}
      (fun E : X.QCoh => E.obj.IsKappaGenerated κ) := by
  let P : ObjectProperty X.QCoh := fun E => E.obj.IsKappaGenerated κ
  have h_map : ObjectProperty.EssentiallySmall.{u + 1} (P.map (inclusion X)) := by
    exact @ObjectProperty.EssentiallySmall.of_le.{u + 1, u, u + 1}
      X.Modules inferInstance (P.map (inclusion X))
      (fun M : X.Modules => M.IsKappaGenerated κ)
      (SheafOfModules.IsKappaGenerated.essentiallySmall (R := X.ringCatSheaf) κ)
      (by
        rintro M ⟨E, hE, ⟨e⟩⟩
        exact (SheafOfModules.isKappaGenerated_iff_of_iso e κ).mp hE)
  have h_fiber : ∀ M : X.Modules,
      ObjectProperty.EssentiallySmall.{u + 1}
        (P ⊓ fun E => Nonempty ((inclusion X).obj E ≅ M)) := by
    intro M
    by_cases hM : ∃ E : X.QCoh,
        E.obj.IsKappaGenerated κ ∧ Nonempty ((inclusion X).obj E ≅ M)
    · obtain ⟨E, hE, ⟨e⟩⟩ := hM
      refine ⟨ObjectProperty.ofObj (fun _ : Unit => E), inferInstance, ?_⟩
      rintro E' ⟨hE', ⟨e'⟩⟩
      refine ⟨E, ⟨()⟩, ⟨?_⟩⟩
      exact (inclusion X).preimageIso (e' ≪≫ e.symm)
    · refine ⟨⊥, inferInstance, ?_⟩
      rintro E ⟨hE, he⟩
      exact (hM ⟨E, hE, he⟩).elim
  exact ObjectProperty.EssentiallySmall.of_functor P (inclusion X) h_map h_fiber

end AlgebraicGeometry.Scheme.QCoh
