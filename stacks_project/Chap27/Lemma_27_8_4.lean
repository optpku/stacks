module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.BasicOpen
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Exact
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A M N P : Type u} [CommRing A]
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]
variable [AddCommGroup P] [Module A P]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
variable (calP : ℤ → Submodule ℤ P)
variable [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
variable [DirectSum.Decomposition calP]
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ]
variable [SetLike.GradedSMul 𝒜 calP]

/- Lemma 27.8.4: the sheaf associated to a graded module on `Proj 𝒜` is the sheaf of locally
representable degree-zero homogeneous fractions. -/
@[stacks 01M7] #check
  (AlgebraicGeometry.Proj.AssociatedModule.sheaf 𝒜 ℳ :
    (AlgebraicGeometry.Proj 𝒜).Modules)

section LocalDescriptions

variable {d e : ℕ} (f : 𝒜 d) (hd : 0 < d) (g : 𝒜 e) (he : 0 < e)

/- On a positive-degree standard open, functions are the degree-zero homogeneous localization
of the graded ring. -/
#check
  (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd :
    CommRingCat.of (HomogeneousLocalization.Away 𝒜 (f : A)) ≅
      Γ(Proj 𝒜, Proj.basicOpen 𝒜 (f : A)))

/- The canonical comparison on a positive-degree standard open is a linear map from degree-zero
homogeneous fractions to associated-sheaf sections. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.awaySectionLinearMap 𝒜 ℳ f hd :
    AlgebraicGeometry.Proj.AssociatedModule.away 𝒜 ℳ f →ₗ[
      HomogeneousLocalization.Away 𝒜 (f : A)]
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
          (AlgebraicGeometry.Proj.AssociatedModule.sectionModule 𝒜 ℳ
            (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))))

/- On a positive-degree standard open, associated-sheaf sections are identified by the
canonical fraction-to-section map. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.awaySectionLinearMap_bijective 𝒜 ℳ f hd :
    Function.Bijective
      (AlgebraicGeometry.Proj.AssociatedModule.awaySectionLinearMap 𝒜 ℳ f hd))

variable (hgf : Proj.basicOpen 𝒜 (g : A) ≤ Proj.basicOpen 𝒜 (f : A))

/- Restriction of functions along `D₊(g) ≤ D₊(f)` is the canonical map of degree-zero
homogeneous localizations. -/
#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayAlgHom 𝒜 f.2 hd g.2 he hgf :
    HomogeneousLocalization.Away 𝒜 (f : A) →ₐ[𝒜 0]
      HomogeneousLocalization.Away 𝒜 (g : A))

/- The standard-open affine-chart identifications intertwine sheaf restriction with the
canonical map of degree-zero homogeneous localizations. -/
#check
  (AlgebraicGeometry.Proj.basicOpenIsoSpec_homOfLE 𝒜 f.2 hd g.2 he hgf :
    (Proj.basicOpenIsoSpec 𝒜 (g : A) g.2 he).hom ≫
          Spec.map (CommRingCat.ofHom
            (homogeneousLocalizationAwayToAwayAlgHom 𝒜 f.2 hd g.2 he hgf).toRingHom) =
      ((Proj 𝒜).homOfLE hgf :
          (Proj.basicOpen 𝒜 (g : A)).toScheme ⟶
            (Proj.basicOpen 𝒜 (f : A)).toScheme) ≫
        (Proj.basicOpenIsoSpec 𝒜 (f : A) f.2 hd).hom)

/- The canonical map from degree zero to global functions is compatible with every positive
standard-open chart. -/
#check
  (AlgebraicGeometry.Proj.awayι_toSpecZero 𝒜 (f : A) f.2 hd :
    AlgebraicGeometry.Proj.awayι 𝒜 (f : A) f.2 hd ≫
        AlgebraicGeometry.Proj.toSpecZero 𝒜 =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (f : A)))))

/- The restriction map on associated-module fractions is the canonical linear comparison of
the two degree-zero homogeneous localizations. -/
#check
  (AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜
      (AlgebraicGeometry.Proj.AssociatedModule.nonnegativeGrading ℳ)
      f.2 hd g.2 he hgf :
    AlgebraicGeometry.homogeneousLocalizationAwayToAwayDegreeZeroModuleMapType 𝒜
      (AlgebraicGeometry.Proj.AssociatedModule.nonnegativeGrading ℳ)
      f.2 hd g.2 he hgf)

/- Restriction of associated-sheaf sections agrees with the canonical localized-module map in
the same direction. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.awaySectionLinearMap_restriction
      𝒜 ℳ f hd g he hgf :
    ∀ z : Proj.AssociatedModule.away 𝒜 ℳ f,
      Proj.AssociatedModule.restrict 𝒜 ℳ hgf
          (Proj.AssociatedModule.awaySection 𝒜 ℳ f hd z) =
        Proj.AssociatedModule.awaySection 𝒜 ℳ g he
          (homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜
            (Proj.AssociatedModule.nonnegativeGrading ℳ) f.2 hd g.2 he hgf z))

/- The degree-zero map to global sections restricts on each positive-degree standard open to
the fraction with denominator one. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.degreeZeroToGlobalSections_away 𝒜 ℳ f hd :
    ∀ m : ℳ 0,
      Proj.AssociatedModule.restrict 𝒜 ℳ
          (show Proj.basicOpen 𝒜 (f : A) ≤ ⊤ from le_top)
          (Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜 ℳ m) =
        Proj.AssociatedModule.awaySection 𝒜 ℳ f hd
          ⟨LocalizedModule.mk (m : M) (1 : Submonoid.powers (f : A)),
            HomogeneousLocalization.Module.mk_mem_degreeZeroPart 𝒜
              (Proj.AssociatedModule.nonnegativeGrading ℳ)
              (Submonoid.powers (f : A)) m (1 : 𝒜 0) (by simp)⟩)

end LocalDescriptions

section StalksAndGlobalSections

variable (x : Proj 𝒜)

/- The structure-sheaf stalk at a projective point is the degree-zero homogeneous localization
at its corresponding homogeneous prime. -/
#check
  (AlgebraicGeometry.Proj.stalkIso 𝒜 x :
    (Proj 𝒜).presheaf.stalk x ≅
      CommRingCat.of
        (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal))

/- The associated-sheaf stalk has a canonical linear map to the degree-zero homogeneous
localization at the corresponding projective point. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.stalkToPointLinearMap 𝒜 ℳ x :
    RingedSpace.stalkModuleCat
        (AlgebraicGeometry.Proj.AssociatedModule.sheaf 𝒜 ℳ) x ⟶
      ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
        (AlgebraicGeometry.Proj.AssociatedModule.atPoint 𝒜 ℳ x))

/- The canonical map from the associated-sheaf stalk to the degree-zero module localization at
the corresponding homogeneous prime is bijective. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.stalkToPointLinearMap_bijective 𝒜 ℳ x :
    Function.Bijective
      (AlgebraicGeometry.Proj.AssociatedModule.stalkToPointLinearMap 𝒜 ℳ x))

/- The canonical ring map from degree zero to global functions is induced by
`Proj.toSpecZero`. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.degreeZeroRingHom 𝒜 :
    𝒜 0 →+* (Proj 𝒜).presheaf.obj (op ⊤))

/- The canonical module map from degree zero to global associated-sheaf sections is linear over
the canonical degree-zero ring map. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜 ℳ :
    ℳ 0 →ₗ[𝒜 0]
      (ModuleCat.restrictScalars (Proj.AssociatedModule.degreeZeroRingHom 𝒜)).obj
        (Proj.AssociatedModule.sectionModule 𝒜 ℳ ⊤))

/- On every stalk, the degree-zero global-section map is the fraction with denominator one. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.degreeZeroToGlobalSections_stalk 𝒜 ℳ x :
    ∀ m : ℳ 0,
      Proj.AssociatedModule.stalkToPointLinearMap 𝒜 ℳ x
          (TopCat.Presheaf.germ (Proj.AssociatedModule.sheaf 𝒜 ℳ).val.presheaf
            ⊤ x trivial (Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜 ℳ m)) =
        Proj.AssociatedModule.degreeZeroAtPoint 𝒜 ℳ m x)

end StalksAndGlobalSections

section Functoriality

variable (φ φ' : M →ₗ[A] N) (ψ : N →ₗ[A] P) (Q : Submonoid A)
variable (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
variable (hφ' : ∀ i : ℤ, Set.MapsTo φ' (ℳ i) (ℵ i))
variable (hψ : ∀ i : ℤ, Set.MapsTo ψ (ℵ i) (calP i))

/- A degree-preserving linear map induces a linear map on every degree-zero homogeneous
localization. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.localizedMap 𝒜 ℳ ℵ φ hφ Q :
    AlgebraicGeometry.Proj.AssociatedModule.localization 𝒜 ℳ Q →ₗ[
      HomogeneousLocalization 𝒜 Q]
      AlgebraicGeometry.Proj.AssociatedModule.localization 𝒜 ℵ Q)

/- A degree-preserving linear map induces a canonical morphism of associated sheaves. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.map 𝒜 ℳ ℵ φ hφ :
    Proj.AssociatedModule.sheaf 𝒜 ℳ ⟶ Proj.AssociatedModule.sheaf 𝒜 ℵ)

/- Associated-sheaf maps preserve identities. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.map_id 𝒜 ℳ :
    AlgebraicGeometry.Proj.AssociatedModule.map 𝒜 ℳ ℳ LinearMap.id
        (fun i m hm ↦ hm) =
      𝟙 (AlgebraicGeometry.Proj.AssociatedModule.sheaf 𝒜 ℳ))

/- Associated-sheaf maps preserve composition. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.map_comp 𝒜 ℳ ℵ calP φ ψ hφ hψ :
    AlgebraicGeometry.Proj.AssociatedModule.map 𝒜 ℳ calP (ψ.comp φ)
        (fun i ↦ (hψ i).comp (hφ i)) =
      AlgebraicGeometry.Proj.AssociatedModule.map 𝒜 ℳ ℵ φ hφ ≫
        AlgebraicGeometry.Proj.AssociatedModule.map 𝒜 ℵ calP ψ hψ)

/- Associated-sheaf maps preserve zero morphisms. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.map_zero 𝒜 ℳ ℵ :
    AlgebraicGeometry.Proj.AssociatedModule.map 𝒜 ℳ ℵ (0 : M →ₗ[A] N)
        (fun i m hm ↦ (ℵ i).zero_mem) = 0)

/- Associated-sheaf maps preserve addition. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.map_add 𝒜 ℳ ℵ φ φ' hφ hφ' :
    AlgebraicGeometry.Proj.AssociatedModule.map 𝒜 ℳ ℵ (φ + φ')
        (fun i m hm ↦ (ℵ i).add_mem (hφ i hm) (hφ' i hm)) =
      AlgebraicGeometry.Proj.AssociatedModule.map 𝒜 ℳ ℵ φ hφ +
        AlgebraicGeometry.Proj.AssociatedModule.map 𝒜 ℳ ℵ φ' hφ')

/- Standard-open fraction-to-section maps are natural in degree-preserving maps. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.awaySectionLinearMap_naturality
      𝒜 ℳ ℵ φ hφ :
    ∀ {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
      (z : Proj.AssociatedModule.away 𝒜 ℳ f),
      Proj.AssociatedModule.mapSection 𝒜 ℳ ℵ φ hφ
          (Proj.basicOpen 𝒜 (f : A))
          (Proj.AssociatedModule.awaySection 𝒜 ℳ f hd z) =
        Proj.AssociatedModule.awaySection 𝒜 ℵ f hd
          (Proj.AssociatedModule.localizedMap 𝒜 ℳ ℵ φ hφ
            (Submonoid.powers (f : A)) z))

/- The stalk identifications are natural in degree-preserving maps. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.stalkToPointLinearMap_naturality
      𝒜 ℳ ℵ φ hφ :
    ∀ x : Proj 𝒜,
      RingedSpace.moduleStalkHom x (Proj.AssociatedModule.map 𝒜 ℳ ℵ φ hφ) ≫
          Proj.AssociatedModule.stalkToPointLinearMap 𝒜 ℵ x =
        Proj.AssociatedModule.stalkToPointLinearMap 𝒜 ℳ x ≫
          Proj.AssociatedModule.atPointMap 𝒜 ℳ ℵ φ hφ x)

/- The degree-zero maps to global sections are natural in degree-preserving maps. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.degreeZeroToGlobalSections_naturality
      𝒜 ℳ ℵ φ hφ :
    ∀ m : ℳ 0,
      Proj.AssociatedModule.mapSection 𝒜 ℳ ℵ φ hφ ⊤
          (Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜 ℳ m) =
        Proj.AssociatedModule.degreeZeroToGlobalSections 𝒜 ℵ
          (Proj.AssociatedModule.degreeZeroMap 𝒜 ℳ ℵ φ hφ m))

variable (hExact : Function.Exact φ ψ)

/- An exact pair of degree-preserving maps determines its short complex of associated
sheaves. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.mapShortComplex
      𝒜 ℳ ℵ calP φ ψ hφ hψ hExact :
    ShortComplex (AlgebraicGeometry.Proj 𝒜).Modules)

/- Exact pairs of degree-preserving maps induce exact short complexes of associated sheaves. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.map_exact
      𝒜 ℳ ℵ calP φ ψ hφ hψ hExact :
    (AlgebraicGeometry.Proj.AssociatedModule.mapShortComplex
      𝒜 ℳ ℵ calP φ ψ hφ hψ hExact).Exact)

end Functoriality

end AlgebraicGeometry
