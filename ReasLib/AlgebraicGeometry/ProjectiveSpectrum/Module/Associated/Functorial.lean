/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated

/-!
# Functoriality of sheaves associated to graded modules

A degree-preserving linear map between integer-graded modules induces canonical maps on their
degree-zero homogeneous localizations and on their associated sheaves.  These maps preserve the
additive structure and are compatible with standard opens, stalks, and degree-zero global
sections.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u v w

namespace AlgebraicGeometry.Proj.AssociatedModule

variable {R : Type u} {A M N P : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Module A M]
variable [AddCommGroup N] [Module R N] [Module A N]
variable [AddCommGroup P] [Module R P] [Module A P]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (ℳ : ℤ → Submodule R M) (ℵ : ℤ → Submodule R N)
variable (calP : ℤ → Submodule R P)
variable [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℵ]
variable [DirectSum.Decomposition calP]
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ]
variable [SetLike.GradedSMul 𝒜 calP]

/-- Localizing a degree-preserving linear map preserves the degree-zero homogeneous parts. -/
theorem localizedMap_mem_degreeZeroPart (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i)) (Q : Submonoid A)
    (z : localization 𝒜 ℳ Q) :
    LocalizedModule.map Q φ z ∈ localization 𝒜 ℵ Q := sorry

/-- The map on degree-zero homogeneous localizations induced by a degree-preserving linear map. -/
noncomputable def localizedMap (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i)) (Q : Submonoid A) :
    localization 𝒜 ℳ Q →ₗ[HomogeneousLocalization 𝒜 Q] localization 𝒜 ℵ Q where
  toFun z := ⟨LocalizedModule.map Q φ z,
    localizedMap_mem_degreeZeroPart 𝒜 ℳ ℵ φ hφ Q z⟩
  map_add' x y := Subtype.ext ((LocalizedModule.map Q φ).map_add x y)
  map_smul' r x := Subtype.ext ((LocalizedModule.map Q φ).map_smul
    (algebraMap (HomogeneousLocalization 𝒜 Q) (Localization Q) r) x)

/-- Localized degree-preserving maps commute with enlargement from a standard-open denominator
set to the prime complement at a point. -/
theorem localizedMap_awayToPoint (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i)) {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (z : away 𝒜 ℳ f) :
    localizedMap 𝒜 ℳ ℵ φ hφ x.1.asHomogeneousIdeal.toIdeal.primeCompl
        (awayToPoint 𝒜 ℳ f x z) =
      awayToPoint 𝒜 ℵ f x
        (localizedMap 𝒜 ℳ ℵ φ hφ (Submonoid.powers (f : A)) z) := sorry

/-- Applying a degree-preserving localized map pointwise to a locally representable section
again gives a locally representable section. -/
theorem mapSection_isLocallyRepresentable (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (s : sections 𝒜 ℳ U) :
    IsLocallyRepresentable 𝒜 ℵ U
      (fun x ↦ localizedMap 𝒜 ℳ ℵ φ hφ
        x.1.asHomogeneousIdeal.toIdeal.primeCompl (s.1 x)) := sorry

/-- The map on associated sections induced pointwise by a degree-preserving linear map. -/
noncomputable def mapSection (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (s : sections 𝒜 ℳ U) : sections 𝒜 ℵ U :=
  ⟨fun x ↦ localizedMap 𝒜 ℳ ℵ φ hφ
      x.1.asHomogeneousIdeal.toIdeal.primeCompl (s.1 x),
    mapSection_isLocallyRepresentable 𝒜 ℳ ℵ φ hφ U s⟩

/-- The induced map on associated sections sends zero to zero. -/
theorem mapSection_zero (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    mapSection 𝒜 ℳ ℵ φ hφ U 0 = 0 := sorry

/-- The induced map on associated sections preserves addition. -/
theorem mapSection_add (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (s t : sections 𝒜 ℳ U) :
    mapSection 𝒜 ℳ ℵ φ hφ U (s + t) =
      mapSection 𝒜 ℳ ℵ φ hφ U s + mapSection 𝒜 ℳ ℵ φ hφ U t := sorry

set_option synthInstance.maxHeartbeats 200000 in
/-- The induced map on associated sections is linear over the structure-sheaf sections. -/
theorem mapSection_smul (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (r : (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)) (s : sections 𝒜 ℳ U) :
    mapSection 𝒜 ℳ ℵ φ hφ U (r • s) =
      r • mapSection 𝒜 ℳ ℵ φ hφ U s := sorry

/-- The induced maps on associated sections commute with restriction to smaller opens. -/
theorem mapSection_restriction (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    {U V : (AlgebraicGeometry.Proj 𝒜).Opens} (hVU : V ≤ U)
    (s : sections 𝒜 ℳ U) :
    mapSection 𝒜 ℳ ℵ φ hφ V (restrict 𝒜 ℳ hVU s) =
      restrict 𝒜 ℵ hVU (mapSection 𝒜 ℳ ℵ φ hφ U s) := sorry

/-- The linear morphism on the module of associated sections over one open. -/
noncomputable def mapSectionLinearMap (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    sectionModule 𝒜 ℳ U ⟶ sectionModule 𝒜 ℵ U :=
  ModuleCat.ofHom
    { toFun := mapSection 𝒜 ℳ ℵ φ hφ U
      map_add' := mapSection_add 𝒜 ℳ ℵ φ hφ U
      map_smul' := mapSection_smul 𝒜 ℳ ℵ φ hφ U }

/-- The morphism of associated sheaves induced by a degree-preserving linear map. -/
noncomputable def map (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i)) :
    sheaf 𝒜 ℳ ⟶ sheaf 𝒜 ℵ :=
  ⟨PresheafOfModules.Hom.mk
    (fun U ↦ mapSectionLinearMap 𝒜 ℳ ℵ φ hφ U.unop)
    (fun {U V} i ↦ by
      ext s
      exact mapSection_restriction 𝒜 ℳ ℵ φ hφ i.unop.le s)⟩

/-- The associated-sheaf map induced by the identity linear map is the identity morphism. -/
theorem map_id :
    map 𝒜 ℳ ℳ LinearMap.id (fun _ _ hx ↦ hx) = 𝟙 (sheaf 𝒜 ℳ) := sorry

/-- Associated-sheaf maps preserve composition of degree-preserving linear maps. -/
theorem map_comp (φ : M →ₗ[A] N) (ψ : N →ₗ[A] P)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (hψ : ∀ i : ℤ, Set.MapsTo ψ (ℵ i) (calP i)) :
    map 𝒜 ℳ calP (ψ.comp φ) (fun i ↦ (hψ i).comp (hφ i)) =
      map 𝒜 ℳ ℵ φ hφ ≫ map 𝒜 ℵ calP ψ hψ := sorry

/-- The zero degree-preserving linear map induces the zero associated-sheaf morphism. -/
theorem map_zero :
    map 𝒜 ℳ ℵ (0 : M →ₗ[A] N) (fun i _ _ ↦ (ℵ i).zero_mem) = 0 := sorry

/-- The associated-sheaf construction preserves addition of degree-preserving linear maps. -/
theorem map_add (φ ψ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (hψ : ∀ i : ℤ, Set.MapsTo ψ (ℳ i) (ℵ i)) :
    map 𝒜 ℳ ℵ (φ + ψ)
        (fun i _ hx ↦ (ℵ i).add_mem (hφ i hx) (hψ i hx)) =
      map 𝒜 ℳ ℵ φ hφ + map 𝒜 ℳ ℵ ψ hψ := sorry

/-- On a positive-degree standard open, the associated-sheaf map agrees with the localized
degree-preserving linear map under the canonical fraction-to-section maps. -/
theorem awaySectionLinearMap_naturality (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i)) {d : ℕ}
    (f : 𝒜 d) (hd : 0 < d) (z : away 𝒜 ℳ f) :
    mapSection 𝒜 ℳ ℵ φ hφ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
        (awaySection 𝒜 ℳ f hd z) =
      awaySection 𝒜 ℵ f hd
        (localizedMap 𝒜 ℳ ℵ φ hφ (Submonoid.powers (f : A)) z) := sorry

/-- The map between point localizations induced by a degree-preserving linear map, regarded as
a morphism over the structure-sheaf stalk. -/
noncomputable def atPointMap (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (x : AlgebraicGeometry.Proj 𝒜) :
    ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) (atPoint 𝒜 ℳ x) ⟶
      ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) (atPoint 𝒜 ℵ x) :=
  (ModuleCat.restrictScalars (AlgebraicGeometry.Proj.stalkIso 𝒜 x).hom.hom).map
    (ModuleCat.ofHom (localizedMap 𝒜 ℳ ℵ φ hφ
      x.asHomogeneousIdeal.toIdeal.primeCompl))

/-- The canonical identifications of associated-sheaf stalks with point localizations are
natural in degree-preserving linear maps. -/
theorem stalkToPointLinearMap_naturality (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i))
    (x : AlgebraicGeometry.Proj 𝒜) :
    RingedSpace.moduleStalkHom x (map 𝒜 ℳ ℵ φ hφ) ≫
        stalkToPointLinearMap 𝒜 ℵ x =
      stalkToPointLinearMap 𝒜 ℳ x ≫ atPointMap 𝒜 ℳ ℵ φ hφ x := sorry

/-- The restriction of a degree-preserving map to the degree-zero homogeneous pieces. -/
noncomputable def degreeZeroMap (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i)) : ℳ 0 →ₗ[𝒜 0] ℵ 0 where
  toFun m := ⟨φ m, hφ 0 m.2⟩
  map_add' := fun _ _ ↦ Subtype.ext (φ.map_add _ _)
  map_smul' := fun r m ↦ Subtype.ext (φ.map_smul (r : A) (m : M))

/-- The canonical maps from degree-zero pieces to global sections are natural in
degree-preserving linear maps. -/
theorem degreeZeroToGlobalSections_naturality (φ : M →ₗ[A] N)
    (hφ : ∀ i : ℤ, Set.MapsTo φ (ℳ i) (ℵ i)) (m : ℳ 0) :
    mapSection 𝒜 ℳ ℵ φ hφ ⊤ (degreeZeroToGlobalSections 𝒜 ℳ m) =
      degreeZeroToGlobalSections 𝒜 ℵ (degreeZeroMap 𝒜 ℳ ℵ φ hφ m) := sorry

end AlgebraicGeometry.Proj.AssociatedModule
