module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import Mathlib.RepresentationTheory.Rep.Iso
public import ReasLib.RepresentationTheory.Coinvariants.Complex
public import ReasLib.RepresentationTheory.Coinvariants.Functor
public import ReasLib.RepresentationTheory.MonoidAlgebra.Trivial

/-!
# Coinvariants of restricted projective resolutions
-/

public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped MonoidAlgebra

noncomputable section

universe u

namespace MonoidAlgebra

section RingCoefficients

variable {Λ G Γ : Type u} [Ring Λ] [Group G] [Monoid Γ]
variable (S : NatMonoidExtension G Γ)

/-- Restriction of a monoid-algebra complex along the kernel-group inclusion. -/
@[expose, reducible] def restrictModuleComplex
    (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ) :
    ChainComplex (ModuleCat.{u} (Λ[G])) ℕ :=
  ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj P

private def restrictModuleTrivialIso :
    (ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj (trivialModule Λ Γ) ≅
      trivialModule Λ G :=
  (ModuleCat.restrictScalarsComp'App (mapDomainRingHom Λ S.inl)
    (augmentation Λ Γ) (augmentation Λ G) (by
      apply MonoidAlgebra.ringHom_ext <;> intro x <;>
        simp [mapDomainRingHom_apply]) (ModuleCat.of Λ Λ)).symm

variable (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)

/-- The restricted augmentation onto the trivial kernel-group module. -/
def restrictModuleπ
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ)) :
    restrictModuleComplex S P ⟶
      (ChainComplex.single₀ (ModuleCat.{u} (Λ[G]))).obj (trivialModule Λ G) :=
  (ChainComplex.toSingle₀Equiv (restrictModuleComplex S P) (trivialModule Λ G)).symm
    ⟨(ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).map (ε.f 0) ≫
        (restrictModuleTrivialIso S).hom, by
      change (ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).map (P.d 1 0) ≫
        ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).map (ε.f 0) ≫
          (restrictModuleTrivialIso S).hom) = 0
      rw [← Category.assoc, ← Functor.map_comp]
      have h : P.d 1 0 ≫ ε.f 0 = 0 :=
        (ChainComplex.toSingle₀Equiv P (trivialModule Λ Γ) ε).property
      rw [h, Functor.map_zero, zero_comp]⟩

/-- Scalar restriction preserves a quasi-isomorphic augmentation to the trivial module. -/
instance instQuasiIso_restrictModuleπ
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] : QuasiIso (restrictModuleπ S P ε) := by
  sorry

variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [hRestriction : ∀ n, IsRestrictionAlongInl Λ S (P.X n)]

private def restrictModuleCarrierLinearEquiv (M : ModuleCat.{u} (Λ[Γ]))
    [Module Λ M] [IsScalarTower Λ (Λ[Γ]) M] :
    (ModuleCat.restrictScalars (singleOneRingHom : Λ →+* Λ[G])).obj
      ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj M) ≃ₗ[Λ] M :=
  { AddEquiv.refl _ with
    map_smul' := fun a x ↦ by
      change mapDomainRingHom Λ S.inl (single 1 a) • (show M from x) =
        a • (show M from x)
      simpa [mapDomainRingHom_apply, one_def, smul_single] using
        (smul_one_smul (Λ[Γ]) a (show M from x)) }

private def restrictedToCoinvariants (M : ModuleCat.{u} (Λ[Γ]))
    [Module (Λ[G]) M] [Module Λ M] [IsScalarTower Λ (Λ[Γ]) M]
    [IsRestrictionAlongInl Λ S M] :
    (Coinvariants.functor Λ G).obj
      ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj M) →ₗ[Λ]
        Coinvariants Λ G M :=
  Coinvariants.lift Λ G _
    ((Coinvariants.mk Λ G M).comp (restrictModuleCarrierLinearEquiv S M).toLinearMap)
    fun g x ↦ by
      change Coinvariants.mk Λ G M
          (mapDomainRingHom Λ S.inl (single g 1) • (show M from x)) =
        Coinvariants.mk Λ G M (show M from x)
      rw [← IsRestrictionAlongInl.smul_eq, Coinvariants.mk_smul]

private def restrictedFromCoinvariants (M : ModuleCat.{u} (Λ[Γ]))
    [Module (Λ[G]) M] [Module Λ M] [IsScalarTower Λ (Λ[Γ]) M]
    [IsRestrictionAlongInl Λ S M] :
    Coinvariants Λ G M →ₗ[Λ] (Coinvariants.functor Λ G).obj
      ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj M) :=
  Coinvariants.lift Λ G M
    ((Coinvariants.mk Λ G _).comp (restrictModuleCarrierLinearEquiv S M).symm.toLinearMap)
    fun g x ↦ by
      have h : (restrictModuleCarrierLinearEquiv S M).symm
          ((single g (1 : Λ) : Λ[G]) • x) =
          (single g (1 : Λ) : Λ[G]) • (restrictModuleCarrierLinearEquiv S M).symm x := by
        change (single g (1 : Λ) : Λ[G]) • x =
          mapDomainRingHom Λ S.inl (single g 1) • x
        exact IsRestrictionAlongInl.smul_eq _ _
      change Coinvariants.mk Λ G _ ((restrictModuleCarrierLinearEquiv S M).symm
          ((single g (1 : Λ) : Λ[G]) • x)) =
        Coinvariants.mk Λ G _ ((restrictModuleCarrierLinearEquiv S M).symm x)
      rw [h, Coinvariants.mk_smul]

private def restrictedCoinvariantsIso (M : ModuleCat.{u} (Λ[Γ]))
    [Module (Λ[G]) M] [Module Λ M] [IsScalarTower Λ (Λ[Γ]) M]
    [IsRestrictionAlongInl Λ S M] :
    (Coinvariants.functor Λ G).obj
      ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj M) ≅
        ModuleCat.of Λ (Coinvariants Λ G M) where
  hom := ModuleCat.ofHom (restrictedToCoinvariants S M)
  inv := ModuleCat.ofHom (restrictedFromCoinvariants S M)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply Coinvariants.hom_ext Λ G _
    ext x
    change restrictedFromCoinvariants S M
      (restrictedToCoinvariants S M (Coinvariants.mk Λ G _ x)) =
        Coinvariants.mk Λ G _ x
    simp [restrictedToCoinvariants, restrictedFromCoinvariants, Coinvariants.functor,
      Coinvariants.lift_mk]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply Coinvariants.hom_ext Λ G M
    ext x
    change restrictedToCoinvariants S M
      (restrictedFromCoinvariants S M (Coinvariants.mk Λ G M x)) =
        Coinvariants.mk Λ G M x
    simp [restrictedToCoinvariants, restrictedFromCoinvariants, Coinvariants.functor,
      Coinvariants.lift_mk]

/-- Functorial coinvariants of the restricted complex identify with the complex of
explicit quotient modules and descended differentials. -/
def Coinvariants.restrictModuleComplexIso :
    ((Coinvariants.functor Λ G).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (restrictModuleComplex S P) ≅ Coinvariants.complex S P :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ restrictedCoinvariantsIso S (P.X n))
    fun i j hij ↦ by
      obtain rfl : i = j + 1 := hij.symm
      apply ModuleCat.hom_ext
      erw [ModuleCat.hom_comp, Coinvariants.complex_d, ModuleCat.hom_comp]
      apply Coinvariants.hom_ext Λ G _
      ext x
      change Coinvariants.d S P j
          (restrictedToCoinvariants S (P.X (j + 1)) (Coinvariants.mk Λ G _ x)) =
        restrictedToCoinvariants S (P.X j)
          ((Coinvariants.functor Λ G).map
            ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).map (P.d (j + 1) j))
            (Coinvariants.mk Λ G _ x))
      rw [Coinvariants.functor_map_mk]
      simp only [restrictedToCoinvariants, Coinvariants.functor, Coinvariants.lift_mk, LinearMap.comp_apply,
        LinearEquiv.coe_coe, Coinvariants.d]
      rfl

variable [Finite G] [hFinite : ∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [hProjective : ∀ n, Module.Projective (Λ[G]) (P.X n)]

include hRestriction hFinite hProjective in
/-- Compatible finite projective kernel-group actions give projective restricted terms. -/
instance instProjective_restrictModuleComplex (n : ℕ) :
    Projective ((restrictModuleComplex S P).X n) := by
  sorry

/-- A quasi-isomorphic augmentation with projective restricted terms gives a projective
resolution of the trivial kernel-group module. -/
def restrictModuleResolution
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] : ProjectiveResolution (trivialModule Λ G) where
  complex := restrictModuleComplex S P
  π := restrictModuleπ S P ε

/-- Homology of the coinvariants complex computes the left-derived coinvariants of
the trivial kernel-group module over an arbitrary coefficient ring. -/
def Coinvariants.homologyIso_leftDerived
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (n : ℕ) :
    (Coinvariants.complex S P).homology n ≅
      ((Coinvariants.functor Λ G).leftDerived n).obj (trivialModule Λ G) :=
  (homologyFunctor (ModuleCat.{u} Λ) (ComplexShape.down ℕ) n).mapIso
      (Coinvariants.restrictModuleComplexIso S P).symm ≪≫
    ((restrictModuleResolution S P ε).isoLeftDerivedObj (Coinvariants.functor Λ G) n).symm

end RingCoefficients

variable {Λ G Γ : Type u} [CommRing Λ] [Group G] [Monoid Γ]
variable (S : NatMonoidExtension G Γ)

/-- Restriction along the kernel inclusion, followed by conversion to a representation. -/
@[expose, reducible] def restrictToRep : ModuleCat.{u} (Λ[Γ]) ⥤ Rep.{u} Λ G :=
  ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl) ⋙ Rep.ofModuleMonoidAlgebra

/-- A monoid-algebra complex restricted to a complex of kernel-group representations. -/
@[expose, reducible] def restrictComplex (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ) :
    ChainComplex (Rep.{u} Λ G) ℕ :=
  ((restrictToRep S).mapHomologicalComplex (ComplexShape.down ℕ)).obj P

/-- The restricted complex has the termwise restricted representations as its terms. -/
theorem restrictComplex_X (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ) (n : ℕ) :
    (restrictComplex S P).X n = (restrictToRep S).obj (P.X n) := rfl

/-- The carrier identification of a restricted representation is coefficient-linear when
the original coefficient action is compatible with its monoid-algebra action. -/
def restrictCarrierLinearEquiv (M : ModuleCat.{u} (Λ[Γ])) [Module Λ M]
    [IsScalarTower Λ (Λ[Γ]) M] : ((restrictToRep S).obj M).V ≃ₗ[Λ] M :=
  { AddEquiv.refl _ with
    map_smul' := fun a x ↦ by
      change mapDomainRingHom Λ S.inl (algebraMap Λ (Λ[G]) a) • (show M from x) =
        a • (show M from x)
      rw [mapDomainRingHom_apply, mapDomain_algebraMap]
      exact algebraMap_smul (Λ[Γ]) a (show M from x) }

private theorem restrictCarrier_ρ (M : ModuleCat.{u} (Λ[Γ]))
    [Module (Λ[G]) M] [Module Λ M] [IsScalarTower Λ (Λ[Γ]) M]
    [IsRestrictionAlongInl Λ S M] (g : G) (x : ((restrictToRep S).obj M).V) :
    restrictCarrierLinearEquiv S M (((restrictToRep S).obj M).ρ g x) =
      (single g (1 : Λ) : Λ[G]) • restrictCarrierLinearEquiv S M x := by
  change mapDomainRingHom Λ S.inl (single g 1) • (show M from x) =
    (single g (1 : Λ) : Λ[G]) • (show M from x)
  exact (IsRestrictionAlongInl.smul_eq _ _).symm

/-- Restricting the trivial monoid-algebra module gives the trivial kernel-group representation. -/
def restrictTrivialIso :
    (restrictToRep S).obj (trivialModule Λ Γ) ≅ Rep.trivial Λ G Λ :=
  Rep.mkIso (ρ := ((restrictToRep S).obj (trivialModule Λ Γ)).ρ)
    (σ := (Rep.trivial Λ G Λ).ρ) (Representation.Equiv.mk
    (ρ := ((restrictToRep S).obj (trivialModule Λ Γ)).ρ)
    (σ := (Rep.trivial Λ G Λ).ρ)
    (show ((restrictToRep S).obj (trivialModule Λ Γ)).V ≃ₗ[Λ] Λ from
    { AddEquiv.refl _ with
      map_smul' := fun a x ↦ by
        change augmentation Λ Γ (mapDomainRingHom Λ S.inl (algebraMap Λ (Λ[G]) a)) •
          (show Λ from x) = a • (show Λ from x)
        simp [mapDomainRingHom_apply, coe_algebraMap] })
    fun g ↦ by
      ext x
      change augmentation Λ Γ (mapDomainRingHom Λ S.inl (single g 1)) •
        (show Λ from x) = x
      simp [mapDomainRingHom_apply])

variable (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [hRestriction : ∀ n, IsRestrictionAlongInl Λ S (P.X n)]

/-- The augmentation of a complex restricted to kernel-group representations. -/
def restrictπ
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ)) :
    restrictComplex S P ⟶
      (ChainComplex.single₀ (Rep.{u} Λ G)).obj (Rep.trivial Λ G Λ) :=
  (ChainComplex.toSingle₀Equiv (restrictComplex S P) (Rep.trivial Λ G Λ)).symm
    ⟨(restrictToRep S).map (ε.f 0) ≫ (restrictTrivialIso S).hom, by
      change (restrictToRep S).map (P.d 1 0) ≫
        ((restrictToRep S).map (ε.f 0) ≫ (restrictTrivialIso S).hom) = 0
      rw [← Category.assoc, ← Functor.map_comp]
      have h : P.d 1 0 ≫ ε.f 0 = 0 :=
        (ChainComplex.toSingle₀Equiv P (trivialModule Λ Γ) ε).property
      rw [h, Functor.map_zero, zero_comp]⟩

/-- Restriction preserves a quasi-isomorphic augmentation onto the trivial module. -/
instance instQuasiIso_restrictπ
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] : QuasiIso (restrictπ S P ε) := by
  sorry

variable {P} in
private def toCoinvariants (M : ModuleCat.{u} (Λ[Γ]))
    [Module (Λ[G]) M] [Module Λ M] [IsScalarTower Λ (Λ[Γ]) M]
    [IsRestrictionAlongInl Λ S M] :
    Representation.Coinvariants ((restrictToRep S).obj M).ρ →ₗ[Λ] Coinvariants Λ G M :=
  Representation.Coinvariants.lift _
    ((Coinvariants.mk Λ G M).comp (restrictCarrierLinearEquiv S M).toLinearMap)
    fun g ↦ by
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, restrictCarrier_ρ,
        Coinvariants.mk_smul]

variable {P} in
private def fromCoinvariants (M : ModuleCat.{u} (Λ[Γ]))
    [Module (Λ[G]) M] [Module Λ M] [IsScalarTower Λ (Λ[Γ]) M]
    [IsRestrictionAlongInl Λ S M] :
    Coinvariants Λ G M →ₗ[Λ] Representation.Coinvariants ((restrictToRep S).obj M).ρ :=
  Coinvariants.lift Λ G M
    ((Representation.Coinvariants.mk ((restrictToRep S).obj M).ρ).comp
      (restrictCarrierLinearEquiv S M).symm.toLinearMap)
    fun g x ↦ by
      change Representation.Coinvariants.mk ((restrictToRep S).obj M).ρ
        ((restrictCarrierLinearEquiv S M).symm ((single g (1 : Λ) : Λ[G]) • x)) =
          Representation.Coinvariants.mk ((restrictToRep S).obj M).ρ
            ((restrictCarrierLinearEquiv S M).symm x)
      have h : (restrictCarrierLinearEquiv S M).symm ((single g (1 : Λ) : Λ[G]) • x) =
          ((restrictToRep S).obj M).ρ g ((restrictCarrierLinearEquiv S M).symm x) := by
        apply (restrictCarrierLinearEquiv S M).injective
        rw [LinearEquiv.apply_symm_apply, restrictCarrier_ρ, LinearEquiv.apply_symm_apply]
      rw [h, Representation.Coinvariants.mk_self_apply]

/-- The canonical quotient comparison between representation coinvariants and
monoid-algebra coinvariants with compatible coefficient actions. -/
def coinvariantsModuleIso (M : ModuleCat.{u} (Λ[Γ]))
    [Module (Λ[G]) M] [Module Λ M] [IsScalarTower Λ (Λ[Γ]) M]
    [IsScalarTower Λ (Λ[G]) M] [IsRestrictionAlongInl Λ S M] :
    (Rep.coinvariantsFunctor Λ G).obj ((restrictToRep S).obj M) ≅
      ModuleCat.of Λ (Coinvariants Λ G M) where
  hom := ModuleCat.ofHom (toCoinvariants S M)
  inv := ModuleCat.ofHom (fromCoinvariants S M)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Representation.Coinvariants.induction_on x fun x ↦ ?_
    simp [toCoinvariants, fromCoinvariants, Representation.Coinvariants.lift_mk,
      Coinvariants.lift_mk]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective Λ G M x
    simp [toCoinvariants, fromCoinvariants, Representation.Coinvariants.lift_mk,
      Coinvariants.lift_mk]

/-- Tensoring with the trivial coefficient representation and taking coinvariants
recovers the termwise monoid-algebra coinvariant module. -/
def coinvariantsTensorObjIso (n : ℕ) :
    (HomologicalComplex.coinvariantsTensorObj (Rep.trivial Λ G Λ)
        (restrictComplex S P)).X n ≅ (Coinvariants.complex S P).X n :=
  (Rep.coinvariantsFunctor Λ G).mapIso (λ_ ((restrictComplex S P).X n)) ≪≫
    coinvariantsModuleIso S (P.X n)

private theorem coinvariantsModuleIso_comm_d (n : ℕ) :
    (coinvariantsModuleIso S (P.X (n + 1))).hom ≫ (Coinvariants.complex S P).d (n + 1) n =
      (Rep.coinvariantsFunctor Λ G).map ((restrictComplex S P).d (n + 1) n) ≫
        (coinvariantsModuleIso S (P.X n)).hom := by
  apply ModuleCat.hom_ext
  erw [ModuleCat.hom_comp, Coinvariants.complex_d, ModuleCat.hom_comp]
  apply LinearMap.ext
  intro x
  refine Representation.Coinvariants.induction_on x fun x ↦ ?_
  change Coinvariants.d S P n (toCoinvariants S (P.X (n + 1))
      (Representation.Coinvariants.mk _ x)) =
    toCoinvariants S (P.X n) (Representation.Coinvariants.map _ _
      ((restrictComplex S P).d (n + 1) n).hom (Representation.Coinvariants.mk _ x))
  rw [Representation.Coinvariants.map_mk]
  simp only [toCoinvariants, Representation.Coinvariants.lift_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Coinvariants.d, Coinvariants.lift_mk]
  rfl

/-- The tensor-coinvariants complex of the restricted complex is isomorphic to
the complex formed from the explicit descended differentials. -/
def coinvariantsTensorComplexIso :
    HomologicalComplex.coinvariantsTensorObj (Rep.trivial Λ G Λ) (restrictComplex S P) ≅
      Coinvariants.complex S P :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ coinvariantsTensorObjIso S P n)
    fun i j hij ↦ by
      obtain rfl : i = j + 1 := hij.symm
      change (Rep.coinvariantsFunctor Λ G).map (λ_ ((restrictComplex S P).X (j + 1))).hom ≫
          ((coinvariantsModuleIso S (P.X (j + 1))).hom ≫ (Coinvariants.complex S P).d (j + 1) j) =
        (Rep.coinvariantsFunctor Λ G).map
            (Rep.trivial Λ G Λ ◁ (restrictComplex S P).d (j + 1) j) ≫
          ((Rep.coinvariantsFunctor Λ G).map (λ_ ((restrictComplex S P).X j)).hom ≫
            (coinvariantsModuleIso S (P.X j)).hom)
      erw [coinvariantsModuleIso_comm_d S P j]
      change (Rep.coinvariantsFunctor Λ G).map
          (λ_ ((restrictToRep S).obj (P.X (j + 1)))).hom ≫
          ((Rep.coinvariantsFunctor Λ G).map ((restrictToRep S).map (P.d (j + 1) j)) ≫
            (coinvariantsModuleIso S (P.X j)).hom) =
        (Rep.coinvariantsFunctor Λ G).map
          (Rep.trivial Λ G Λ ◁ (restrictToRep S).map (P.d (j + 1) j)) ≫
          ((Rep.coinvariantsFunctor Λ G).map (λ_ ((restrictToRep S).obj (P.X j))).hom ≫
            (coinvariantsModuleIso S (P.X j)).hom)
      rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc,
        ← Functor.map_comp]
      exact congrArg
        (fun f ↦ (Rep.coinvariantsFunctor Λ G).map f ≫ (coinvariantsModuleIso S (P.X j)).hom)
        (leftUnitor_naturality ((restrictToRep S).map (P.d (j + 1) j))).symm

variable [Finite G] [hFinite : ∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [hProjective : ∀ n, Module.Projective (Λ[G]) (P.X n)]

include hRestriction hFinite hProjective in
/-- Finite projective kernel-group modules restrict to projective representations. -/
instance instProjective_restrictComplex (n : ℕ) :
    Projective ((restrictComplex S P).X n) := by
  sorry

/-- A quasi-isomorphically augmented complex with projective restricted terms
gives a projective resolution of the trivial kernel-group representation. -/
def restrictResolution
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] : ProjectiveResolution (Rep.trivial Λ G Λ) where
  complex := restrictComplex S P
  π := restrictπ S P ε

/-- Homology of the explicit coinvariants complex computes trivial-coefficient group homology. -/
def Coinvariants.homologyIso
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (n : ℕ) :
    (Coinvariants.complex S P).homology n ≅ groupHomology (Rep.trivial Λ G Λ) n := by
  classical
  exact (homologyFunctor (ModuleCat.{u} Λ) (ComplexShape.down ℕ) n).mapIso
      (coinvariantsTensorComplexIso S P).symm ≪≫
    (groupHomologyIso (Rep.trivial Λ G Λ) n (restrictResolution S P ε)).symm

/-- Homology of the explicit coinvariants complex computes Tor with trivial coefficients. -/
def Coinvariants.homologyIso_tor
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (n : ℕ) :
    (Coinvariants.complex S P).homology n ≅
      ((Rep.Tor Λ G n).obj (Rep.trivial Λ G Λ)).obj (Rep.trivial Λ G Λ) := by
  classical
  exact Coinvariants.homologyIso S P ε n ≪≫ groupHomologyIsoTor (Rep.trivial Λ G Λ) n

end MonoidAlgebra
