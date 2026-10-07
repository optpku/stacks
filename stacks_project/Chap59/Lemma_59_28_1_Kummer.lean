module

public import ReasLib.Algebra.Category.Ring.Sheaf.Kummer

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! Compatibility checks for the generic Kummer construction. -/

#check (CategoryTheory.Sheaf.unitsNsmul :
  ∀ (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ),
    CategoryTheory.Sheaf.unitsAddSheaf 𝒪 ⟶ CategoryTheory.Sheaf.unitsAddSheaf 𝒪)
#check (CategoryTheory.Sheaf.rootsOfUnityAddSheaf :
  Sheaf J CommRingCat.{max u v} → ℕ → Sheaf J AddCommGrpCat.{max u v})
#check (CategoryTheory.Sheaf.kummerAddShortComplex :
  Sheaf J CommRingCat.{max u v} → ℕ → ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
#check (CategoryTheory.Sheaf.unitsNsmul_app :
  ∀ (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ) (U : Cᵒᵖ),
    (CategoryTheory.Sheaf.unitsNsmul 𝒪 n).hom.app U =
      AddCommGrpCat.ofHom (nsmulAddMonoidHom n))
#check (CategoryTheory.Sheaf.rootsOfUnityAddSheaf_eq_kernel :
  ∀ (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ),
    CategoryTheory.Sheaf.rootsOfUnityAddSheaf 𝒪 n =
      CategoryTheory.Limits.kernel (CategoryTheory.Sheaf.unitsNsmul 𝒪 n))
#check (CategoryTheory.Sheaf.kummerAddShortComplex_f :
  ∀ (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ),
    (CategoryTheory.Sheaf.kummerAddShortComplex 𝒪 n).f =
      CategoryTheory.Limits.kernel.ι (CategoryTheory.Sheaf.unitsNsmul 𝒪 n))
#check (CategoryTheory.Sheaf.kummerAddShortComplex_g :
  ∀ (𝒪 : Sheaf J CommRingCat.{max u v}) (n : ℕ),
    (CategoryTheory.Sheaf.kummerAddShortComplex 𝒪 n).g =
      CategoryTheory.Sheaf.unitsNsmul 𝒪 n)

end
