module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.Basic

/-!
# Composition of maps between relative projective spectra

This file constructs the composite domain, restricted morphism, and degreewise twist comparison
for composable maps between relative projective spectra.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RelativeProjMap

variable {S X Y Z : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}
variable
  {P𝒜 : RelativeProjPresentation pX}
  {Pℬ : RelativeProjPresentation pY}
  {P𝒞 : RelativeProjPresentation pZ}
  {φ : P𝒜.algebra ⟶ Pℬ.algebra}
  {ψ : Pℬ.algebra ⟶ P𝒞.algebra}

/-- The image open in the final scheme of the inverse image of the first map's domain under the
second map. -/
abbrev compDomain
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ) : Z.Opens :=
  rψ.domain.ι ''ᵁ (rψ.map ⁻¹ᵁ rφ.domain)

/-- The composite morphism on the image-open composite domain. -/
abbrev compMap
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ) :
    (compDomain rφ rψ).toScheme ⟶ X :=
  ((rψ.domain.ι).isoImage (rψ.map ⁻¹ᵁ rφ.domain)).inv ≫
    Scheme.Hom.resLE rψ.map rφ.domain (rψ.map ⁻¹ᵁ rφ.domain) le_rfl ≫
      rφ.map

/-- The intermediate twist on the composite domain obtained by successively pulling back the
target twist of the first map. -/
abbrev compMiddleTwist
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ)
    (n : ℤ) :
    (compDomain rφ rψ).toScheme.Modules :=
  (Scheme.Modules.pullback ((rψ.domain.ι).isoImage (rψ.map ⁻¹ᵁ rφ.domain)).inv).obj
    ((Scheme.Modules.pullback
        (Scheme.Hom.resLE rψ.map rφ.domain (rψ.map ⁻¹ᵁ rφ.domain) le_rfl)).obj
      ((Pℬ.twist n).restrict rφ.domain.ι))

/-- The pullback of the first degreewise twist comparison to the composite domain. -/
abbrev compPullbackTheta
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ)
    (n : ℤ) :
    (Scheme.Modules.pullback (compMap rφ rψ)).obj (P𝒜.twist n) ⟶
      compMiddleTwist rφ rψ n :=
  ((Scheme.Modules.pullbackComp
      (((rψ.domain.ι).isoImage (rψ.map ⁻¹ᵁ rφ.domain)).inv ≫
        Scheme.Hom.resLE rψ.map rφ.domain (rψ.map ⁻¹ᵁ rφ.domain) le_rfl)
      rφ.map).inv.app (P𝒜.twist n)) ≫
    (Scheme.Modules.pullback
        (((rψ.domain.ι).isoImage (rψ.map ⁻¹ᵁ rφ.domain)).inv ≫
          Scheme.Hom.resLE rψ.map rφ.domain (rψ.map ⁻¹ᵁ rφ.domain) le_rfl)).map
      (rφ.theta n) ≫
    ((Scheme.Modules.pullbackComp
        ((rψ.domain.ι).isoImage (rψ.map ⁻¹ᵁ rφ.domain)).inv
        (Scheme.Hom.resLE rψ.map rφ.domain (rψ.map ⁻¹ᵁ rφ.domain) le_rfl)).inv.app
      ((Pℬ.twist n).restrict rφ.domain.ι))

/-- The second degreewise twist comparison restricted to the composite domain. -/
abbrev compThetaPsiOnCompDomain
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ)
    (n : ℤ) :
    compMiddleTwist rφ rψ n ⟶
      (P𝒞.twist n).restrict (compDomain rφ rψ).ι :=
  let V := rψ.map ⁻¹ᵁ rφ.domain
  let a : (compDomain rφ rψ).toScheme ⟶ V.toScheme := ((rψ.domain.ι).isoImage V).inv
  let b : V.toScheme ⟶ rφ.domain.toScheme := Scheme.Hom.resLE rψ.map rφ.domain V le_rfl
  let sourceRestrict :
      (Scheme.Modules.pullback b).obj ((Pℬ.twist n).restrict rφ.domain.ι) ⟶
        ((Scheme.Modules.pullback rψ.map).obj (Pℬ.twist n)).restrict V.ι :=
    (Scheme.Modules.pullback b).map
        ((Scheme.Modules.restrictFunctorIsoPullback rφ.domain.ι).hom.app (Pℬ.twist n)) ≫
      ((Scheme.Modules.pullbackComp b rφ.domain.ι).hom.app (Pℬ.twist n)) ≫
      ((Scheme.Modules.pullbackCongr
          (resLE_comp_ι rψ.map le_rfl)).hom.app (Pℬ.twist n)) ≫
      ((Scheme.Modules.pullbackComp V.ι rψ.map).inv.app (Pℬ.twist n)) ≫
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app
        ((Scheme.Modules.pullback rψ.map).obj (Pℬ.twist n)))
  (Scheme.Modules.pullback a).map sourceRestrict ≫
    (Scheme.Modules.pullback a).map ((Scheme.Modules.restrictFunctor V.ι).map (rψ.theta n)) ≫
    ((Scheme.Modules.restrictFunctorIsoPullback a).inv.app
      (((P𝒞.twist n).restrict rψ.domain.ι).restrict V.ι)) ≫
    ((Scheme.Modules.restrictFunctorComp a V.ι).inv.app
      ((P𝒞.twist n).restrict rψ.domain.ι)) ≫
    ((Scheme.Modules.restrictFunctorComp (a ≫ V.ι) rψ.domain.ι).inv.app
      (P𝒞.twist n)) ≫
    ((Scheme.Modules.restrictFunctorCongr
        (Scheme.Hom.isoImage_inv_ι rψ.domain.ι V)).hom.app
      (P𝒞.twist n)) ≫
    ((Scheme.Modules.restrictFunctorCongr rfl).hom.app
      (P𝒞.twist n))

/-- The degreewise twist comparison for the composite map. -/
abbrev compTheta
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ)
    (n : ℤ) :
    (Scheme.Modules.pullback (compMap rφ rψ)).obj (P𝒜.twist n) ⟶
      (P𝒞.twist n).restrict (compDomain rφ rψ).ι :=
  compPullbackTheta rφ rψ n ≫ compThetaPsiOnCompDomain rφ rψ n

/-- The composite restricted morphism commutes with the structural morphisms to the base. -/
theorem compMap_over_base
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ) :
    compMap rφ rψ ≫ pX = (compDomain rφ rψ).ι ≫ pZ := sorry

/-- The composite of two maps between relative projective spectra. -/
def comp
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ) :
    RelativeProjMap P𝒜 P𝒞 (φ ≫ ψ) where
  domain := compDomain rφ rψ
  map := compMap rφ rψ
  map_over_base := compMap_over_base rφ rψ
  theta := compTheta rφ rψ

/-- The domain of a composite map is its image-open composite domain. -/
theorem comp_domain
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ) :
    (comp rφ rψ).domain = compDomain rφ rψ := rfl

/-- The underlying morphism of a composite map is the restricted composite morphism. -/
theorem comp_map
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ) :
    (comp rφ rψ).map = compMap rφ rψ := rfl

/-- The degreewise comparison of a composite map is the composite twist comparison. -/
theorem comp_theta
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ) :
    ∀ n : ℤ, compTheta rφ rψ n = (comp rφ rψ).theta n :=
  fun _ ↦ rfl

/-- Composition has the specified domain, underlying morphism, and degreewise twist
comparison. -/
theorem comp_spec
    (rφ : RelativeProjMap P𝒜 Pℬ φ)
    (rψ : RelativeProjMap Pℬ P𝒞 ψ) :
    (comp rφ rψ).domain = compDomain rφ rψ ∧
      (comp rφ rψ).map = compMap rφ rψ ∧
        ∀ n : ℤ, compTheta rφ rψ n = (comp rφ rψ).theta n :=
  ⟨comp_domain rφ rψ, comp_map rφ rψ, comp_theta rφ rψ⟩

end RelativeProjMap

end AlgebraicGeometry
