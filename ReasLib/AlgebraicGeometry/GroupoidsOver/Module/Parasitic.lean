/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Abelian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Parasitic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.PresheafModule
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat.Composition
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-! # Stability and descent of parasitic modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory ZeroObject

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- If `F` is a parasitic presheaf of `𝒪_X`-modules and
`g : Y ⟶ X` is a flat morphism of algebraic stacks, then the inverse image
`g⁻¹ F` is parasitic. -/
instance IsParasitic.inverseImage
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (g : Y ⟶ X) [AlgebraicStack.Flat g]
    (F : PresheafOfModules.{u} (structureSheaf X).obj) [IsParasitic F] :
    IsParasitic ((presheafModuleInverseImage g).obj F) where
  isZero_of_flat {U} y hy := by
    letI : AlgebraicStack.Flat (YonedaSlice.representative y) := hy
    let x := (FiberedCategoryOver.Groupoids.fiberFunctor g U).obj y
    let e₀ :
        (FiberedCategoryOver.Groupoids.fiberFunctor
          (YonedaSlice.representative y ≫ g) U).obj
            (BasedCategory.Yoneda.Identity.fiberObj U) ≅ x :=
      (FiberedCategoryOver.Groupoids.fiberFunctor g U).mapIso
        (YonedaSlice.representative.fiberObjIso y)
    let e₁ : YonedaSlice.representative y ≫ g ≅ YonedaSlice.representative x :=
      YonedaSlice.representative.unitIso (YonedaSlice.representative y ≫ g) ≪≫
        FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
          ((ObjectProperty.ι _).mapIso
            ((CartesianBasedFunctor.Yoneda.Chosen.functor X.p U).mapIso e₀))
    have hflat : AlgebraicStack.Flat (YonedaSlice.representative x) := by
      obtain ⟨U', V', a, b, h, ⟨ha, hsurj, hb, ⟨he⟩⟩, hh⟩ :=
        AlgebraicStack.Flat.exists_surjective_smooth_presentation
          (f := YonedaSlice.representative y ≫ g)
      exact ⟨U', V', a, b, h,
        ⟨ha, hsurj, hb, ⟨(Bicategory.whiskerLeftIso a e₁).symm ≪≫ he⟩⟩, hh⟩
    have hz := IsParasitic.isZero_of_flat (F := F) x hflat
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (F.obj (Opposite.op (Functor.Fiber.fiberInclusion.obj x)))
    exact ModuleCat.subsingleton_of_isZero hz

/-- The underlying module presheaf of an object of `Mod(X_τ, 𝒪_X)`, as a
presheaf of modules over the fppf structure sheaf of `X`. -/
def associatedModulePresheaf {X : GroupoidsOver S} {τ : StandardTopology}
    (F : associatedModules X τ) :
    PresheafOfModules.{u} (structureSheaf X).obj :=
  (PresheafOfModules.restrictScalars (associatedStructurePresheafIso X τ).hom).obj F.val

/-- `associatedModulePresheaf F` is restriction of scalars of `F.val` along
`associatedStructurePresheafIso.hom`. -/
theorem associatedModulePresheaf_eq {X : GroupoidsOver S} {τ : StandardTopology}
    (F : associatedModules X τ) :
    associatedModulePresheaf F =
      (PresheafOfModules.restrictScalars
        (associatedStructurePresheafIso X τ).hom).obj F.val := by
  rfl

/-- For `τ` among Zariski, étale, smooth, syntomic, and fppf,
the `τ`-sheafification of a parasitic presheaf of `𝒪_X`-modules is parasitic. -/
instance IsParasitic.sheafification {X : GroupoidsOver S} [AlgebraicStack X]
    (τ : StandardTopology) (F : PresheafOfModules.{u} (structureSheaf X).obj)
    [IsParasitic F] :
    IsParasitic (associatedModulePresheaf
      ((PresheafOfModules.sheafification.{u}
        (associatedStructurePresheafIso X τ).hom).obj F)) := sorry

/-- The object property of parasitic objects of `Mod(X_τ, 𝒪_X)`. -/
abbrev associatedModules.parasitic (X : GroupoidsOver S) [AlgebraicStack X]
    (τ : StandardTopology) : ObjectProperty (associatedModules X τ) :=
  fun F ↦ IsParasitic (associatedModulePresheaf F)

/-- Membership in `associatedModules.parasitic` is parasitic vanishing of the
underlying module presheaf. -/
theorem associatedModules.mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (τ : StandardTopology) (F : associatedModules X τ) :
    associatedModules.parasitic X τ F ↔
      IsParasitic (associatedModulePresheaf F) := by
  rfl

private theorem parasiticPresheavesIsSerreClass
    (X : GroupoidsOver S) [AlgebraicStack X] : IsSerreClass (parasitic X) where
  exists_zero := by
    refine ⟨0, Limits.isZero_zero _, ?_⟩
    constructor
    intro V x hx
    exact (PresheafOfModules.evaluation _ _).map_isZero (Limits.isZero_zero _)
  prop_of_mono := by
    intro F G f hf hG
    constructor
    intro V x hx
    exact Limits.IsZero.of_mono (f.app _) (hG.isZero_of_flat x hx)
  prop_of_epi := by
    intro F G f hf hF
    constructor
    intro V x hx
    exact Limits.IsZero.of_epi (f.app _) (hF.isZero_of_flat x hx)
  prop_X₂_of_shortExact := by
    intro sc hsc h₁ h₃
    constructor
    intro V x hx
    exact (hsc.exact.map_of_mono_of_preservesKernel
      (PresheafOfModules.evaluation _ (Opposite.op (Functor.Fiber.fiberInclusion.obj x)))
        hsc.mono_f inferInstance).isZero_of_both_isZero
      (h₁.isZero_of_flat x hx) (h₃.isZero_of_flat x hx)

/-- For `τ` among Zariski, étale, smooth, syntomic, and fppf,
parasitic objects of `Mod(X_τ, 𝒪_X)` form a Serre subcategory. -/
instance associatedModules.parasiticIsSerreClass
    (X : GroupoidsOver S) [AlgebraicStack X] (τ : StandardTopology) :
    IsSerreClass (associatedModules.parasitic X τ) := by
  let α := (associatedStructurePresheafIso X τ).hom
  let L := PresheafOfModules.sheafification.{u} α
  let U := SheafOfModules.forget.{u} (associatedStructureSheaf X τ) ⋙
    PresheafOfModules.restrictScalars.{u} α
  let adj : L ⊣ U := PresheafOfModules.sheafificationAdjunction.{u} α
  letI : U.IsRightAdjoint := adj.isRightAdjoint
  haveI hc : IsIso adj.counit :=
    inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction.{u} α).counit)
  let P := GroupoidsOver.parasitic X
  letI : P.IsSerreClass := parasiticPresheavesIsSerreClass X
  have hsub : (associatedModules.parasitic X τ).IsClosedUnderSubobjects :=
    inferInstanceAs (P.inverseImage U).IsClosedUnderSubobjects
  letI := hsub
  refine
    { exists_zero := ?_
      prop_of_mono := fun f _ h ↦ (P.inverseImage U).prop_of_mono f h
      prop_of_epi := ?_
      prop_X₂_of_shortExact := ?_ }
  · exact ObjectProperty.ContainsZero.exists_zero (P := P.inverseImage U)
  · intro F G f hf hF
    let sc := (ShortComplex.kernelSequence f).map U
    have hsc : sc.Exact := (ShortComplex.kernelSequence_exact f).map_of_mono_of_preservesKernel
      U inferInstance inferInstance
    let ψ := Limits.cokernel.desc sc.f sc.g sc.zero
    letI hψ : Mono ψ := hsc.mono_cokernelDesc
    haveI hLUf : Epi (L.map (U.map f)) := by
      apply (epi_comp_iff_of_isIso _ (adj.counit.app G)).mp
      change Epi ((U ⋙ L).map f ≫ adj.counit.app G)
      rw [adj.counit.naturality f]
      infer_instance
    haveI hLψ : Epi (L.map ψ) := by
      have hfac : L.map (Limits.cokernel.π sc.f) ≫ L.map ψ = L.map (U.map f) := by
        rw [← L.map_comp]
        exact congrArg L.map (Limits.cokernel.π_desc sc.f sc.g sc.zero)
      exact @epi_of_epi_fac _ _ _ _ _ _ _ _ hLUf hfac
    letI hLψiso : IsIso (L.map ψ) := isIso_of_mono_of_epi _
    have hQ : P (Limits.cokernel sc.f) :=
      P.prop_of_epi (Limits.cokernel.π sc.f) hF
    letI : IsParasitic (Limits.cokernel sc.f) := hQ
    have hLQ : IsParasitic (U.obj (L.obj (Limits.cokernel sc.f))) :=
      IsParasitic.sheafification τ _
    have e : L.obj (Limits.cokernel sc.f) ≅ G :=
      asIso (L.map ψ) ≪≫ (asIso adj.counit).app G
    exact (P.inverseImage U).prop_of_iso e hLQ
  · intro sc hsc h₁ h₃
    constructor
    intro V x hx
    let E := U ⋙ PresheafOfModules.evaluation _
      (Opposite.op (Functor.Fiber.fiberInclusion.obj x))
    have hE : (sc.map E).Exact := hsc.exact.map_of_mono_of_preservesKernel
      E hsc.mono_f inferInstance
    exact hE.isZero_of_both_isZero (h₁.isZero_of_flat x hx) (h₃.isZero_of_flat x hx)

/-- If `F` is an étale `𝒪_X`-module and `f i : Xi i ⟶ X` is a
family of smooth morphisms of algebraic stacks with
`|X| = ⋃ |f i|(|Xi i|)`, and each inverse image `(f i)⁻¹ F` is parasitic, then
`F` is parasitic. -/
theorem IsParasitic.ofSmoothCover {X : GroupoidsOver S}
    [AlgebraicStack X] {ι : Type v} {Xi : ι → GroupoidsOver S}
    [∀ i, AlgebraicStack (Xi i)] (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Smooth (f i)]
    (h_cover : ∀ y : AlgebraicStack.Points X,
      ∃ i, y ∈ Set.range (AlgebraicStack.Points.map (f i)))
    (F : etaleModules X)
    (hF : ∀ i,
      IsParasitic (etaleModulePresheaf ((etaleModuleInverseImage (f i)).obj F))) :
    IsParasitic (etaleModulePresheaf F) := sorry

/-- If `F` is an fppf `𝒪_X`-module and `f i : Xi i ⟶ X` is a
family of flat and locally finitely presented morphisms of algebraic stacks with
`|X| = ⋃ |f i|(|Xi i|)`, and each inverse image `(f i)⁻¹ F` is parasitic, then
`F` is parasitic. -/
theorem IsParasitic.ofFppfCover
    {X : GroupoidsOver S} [AlgebraicStack X] {ι : Type v}
    {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
    (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Flat (f i)]
    [∀ i, AlgebraicStack.LocallyOfFinitePresentation (f i)]
    (h_cover : ∀ y : AlgebraicStack.Points X,
      ∃ i, y ∈ Set.range (AlgebraicStack.Points.map (f i)))
    (F : SheafOfModules.{u} (structureSheaf X))
    (hF : ∀ i, IsParasitic ((presheafModuleInverseImage (f i)).obj F.val)) :
    IsParasitic F.val := sorry

end AlgebraicGeometry.GroupoidsOver
