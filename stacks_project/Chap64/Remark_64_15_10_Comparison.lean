module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
public import Mathlib.RepresentationTheory.Rep.Iso
public import stacks_project.Chap64.Remark_64_15_10_Coinvariants
public import stacks_project.Chap64.Remark_64_15_10_Trivial

/-!
# Restriction of a `Λ[Γ]`-resolution to `G`-representations

This leaf owns restriction of scalars along `S.inl` from `Λ[Γ]`-modules to
`Rep Λ G`, the restricted resolution of the trivial `G`-module, and the
comparison of `(P_•)_G` with mathlib coinvariants.
-/

@[expose] public section

open Ring CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped MonoidAlgebra Ring
open MonoidAlgebra

noncomputable section

universe u

namespace LinearMap.FiniteProjective

variable {Λ G Γ : Type u}
variable [CommRing Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ)
variable (P : ChainComplex (ModuleCat.{u} (Λ[Γ])) ℕ)
variable [∀ n, Module (Λ[G]) (P.X n)] [∀ n, Module Λ (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[Γ]) (P.X n)]
variable [∀ n, IsScalarTower Λ (Λ[G]) (P.X n)]
variable [∀ n, IsRestrictionAlongInl Λ S (P.X n)]
variable [∀ n, Module.Finite (Λ[G]) (P.X n)]
variable [∀ n, Module.Projective (Λ[G]) (P.X n)]

/-- The coefficient action of `Λ` on a `Λ[Γ]`-module. -/
instance instModuleΛ_moduleCat (M : ModuleCat.{u} (Λ[Γ])) : Module Λ M :=
  Module.compHom M (algebraMap Λ (Λ[Γ]))

/-- The `Λ[G]`-module structure on a module restricted along `S.inl`. -/
instance instModule_restrictScalars_inl (M : ModuleCat.{u} (Λ[Γ])) :
    Module (Λ[G]) ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj M) :=
  inferInstanceAs
    (Module (Λ[G]) ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj M))

/-- The coefficient `Λ`-module structure on a module restricted along `S.inl`. -/
instance instModuleΛ_restrictScalars_inl (M : ModuleCat.{u} (Λ[Γ])) :
    Module Λ ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj M) :=
  inferInstanceAs (Module Λ M)

/-- Scalar tower of `Λ` and `Λ[G]` on a module restricted along `S.inl`. -/
instance instIsScalarTower_restrictScalars_inl (M : ModuleCat.{u} (Λ[Γ])) :
    IsScalarTower Λ (Λ[G])
      ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj M) :=
  sorry

/-- Restriction of scalars from `Λ[Γ]`-modules to `G`-representations along `S.inl`. -/
def restrictToRep : ModuleCat.{u} (Λ[Γ]) ⥤ Rep.{u} Λ G where
  obj M :=
    Rep.of
      (Representation.ofModule'
        ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).obj M))
  map f :=
    Rep.ofHom
      { ((ModuleCat.restrictScalars (mapDomainRingHom Λ S.inl)).map f).hom.restrictScalars Λ with
        isIntertwining' := sorry }
  map_id M := sorry
  map_comp f g := sorry

/-- `P` as a complex of `G`-representations by restriction along `S.inl`. -/
def restrictComplex : ChainComplex (Rep.{u} Λ G) ℕ where
  X n := (restrictToRep S).obj (P.X n)
  d i j := (restrictToRep S).map (P.d i j)
  shape i j h := sorry
  d_comp_d' i j k _ _ := sorry

/-- Objects of `restrictComplex` are the termwise restrictions of `P`. -/
theorem restrictComplex_X (n : ℕ) :
    (restrictComplex S P).X n = (restrictToRep S).obj (P.X n) :=
  sorry

/-- Restricted representations of finite projective `Λ[G]`-modules are projective
in `Rep Λ G`. -/
instance instProjective_restrictComplex (n : ℕ) :
    Projective ((restrictComplex S P).X n) :=
  sorry

/-- The additive identification of the restricted carrier with the original
`Λ[Γ]`-module. -/
def restrictCarrierAddEquiv (M : ModuleCat.{u} (Λ[Γ])) :
    ((restrictToRep S).obj M).V ≃+ M :=
  AddEquiv.refl _

/-- The `Λ`-linear map underlying `restrictCarrierAddEquiv`. -/
def restrictCarrier (M : ModuleCat.{u} (Λ[Γ])) [Module Λ M] :
    ((restrictToRep S).obj M).V →ₗ[Λ] M where
  toFun := (restrictCarrierAddEquiv S M).toFun
  map_add' := sorry
  map_smul' := sorry

/-- The inverse `Λ`-linear map underlying `restrictCarrierAddEquiv`. -/
def restrictCarrierSymm (M : ModuleCat.{u} (Λ[Γ])) [Module Λ M] :
    M →ₗ[Λ] ((restrictToRep S).obj M).V where
  toFun := (restrictCarrierAddEquiv S M).invFun
  map_add' := sorry
  map_smul' := sorry

/-- The `Λ`-linear equivalence underlying `restrictCarrierAddEquiv`. -/
def restrictCarrierLinearEquiv (M : ModuleCat.{u} (Λ[Γ])) [Module Λ M] :
    ((restrictToRep S).obj M).V ≃ₗ[Λ] M :=
  { restrictCarrier S M with
    invFun := restrictCarrierSymm S M
    left_inv := sorry
    right_inv := sorry }

/-- The underlying `Λ`-linear equivalence identifying the restricted trivial
`Γ`-module with the coefficient module `Λ`. -/
def restrictTrivialLinearEquiv :
    ((restrictToRep S).obj (trivialModule Λ Γ)).V ≃ₗ[Λ] Λ :=
  restrictCarrierLinearEquiv S (trivialModule Λ Γ)

/-- The restriction of the trivial `Γ`-module is the trivial `G`-module. -/
noncomputable def restrictTrivialIso :
    (restrictToRep S).obj (trivialModule Λ Γ) ≅ Rep.trivial Λ G Λ :=
  Rep.mkIso (Representation.Equiv.mk (restrictTrivialLinearEquiv S) fun _ ↦ sorry)

/-- The augmentation `ε`, restricted along `S.inl` and identified with the
trivial `G`-module. -/
noncomputable def restrictπ
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ)) :
    restrictComplex S P ⟶
      (ChainComplex.single₀ (Rep.{u} Λ G)).obj (Rep.trivial Λ G Λ) :=
  (ChainComplex.toSingle₀Equiv (restrictComplex S P) (Rep.trivial Λ G Λ)).symm
    ⟨(restrictToRep S).map (ε.f 0) ≫ (restrictTrivialIso S).hom, sorry⟩

/-- Restriction of a quasi-isomorphism onto the trivial `Γ`-module remains a
quasi-isomorphism after passage to `Rep Λ G`. -/
instance instQuasiIso_restrictπ
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] :
    QuasiIso (restrictπ S P ε) :=
  sorry

/-- Identification of mathlib coinvariants of the restricted representation with
the source coinvariants `M_G`. -/
noncomputable def coinvariantsModuleIso (M : ModuleCat.{u} (Λ[Γ]))
    [Module (Λ[G]) M] [Module Λ M] [IsRestrictionAlongInl Λ S M] :
    (Rep.coinvariantsFunctor Λ G).obj ((restrictToRep S).obj M) ≅
      ModuleCat.of Λ (Coinvariants Λ G M) where
  hom :=
    ModuleCat.ofHom
      ((Representation.Coinvariants.ker ((restrictToRep S).obj M).ρ).liftQ
        ((Coinvariants.mk Λ G M).comp (restrictCarrier S M)) sorry)
  inv :=
    ModuleCat.ofHom
      ((Coinvariants.ker Λ G M).liftQ
        ((Representation.Coinvariants.mk ((restrictToRep S).obj M).ρ).comp
          (restrictCarrierSymm S M)) sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Termwise identification of `(Λ ⊗ P_•)_G` with the source coinvariants
complex. -/
noncomputable def coinvariantsTensorObjIso (n : ℕ) :
    (HomologicalComplex.coinvariantsTensorObj (Rep.trivial Λ G Λ)
        (restrictComplex S P)).X n ≅
      (Coinvariants.complex S P).X n :=
  (Rep.coinvariantsFunctor Λ G).mapIso (λ_ ((restrictComplex S P).X n)) ≪≫
    coinvariantsModuleIso S (P.X n)

/-- Identification of the mathlib coinvariants-tensor complex of the restricted
resolution with the source coinvariants complex `(P_•)_G`. -/
noncomputable def coinvariantsTensorComplexIso :
    HomologicalComplex.coinvariantsTensorObj (Rep.trivial Λ G Λ) (restrictComplex S P) ≅
      Coinvariants.complex S P :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ coinvariantsTensorObjIso S P n)
    fun _ _ _ ↦ sorry

/-- The restriction of `P_•` along `S.inl`, as a projective resolution of the
trivial `G`-module. -/
noncomputable def restrictResolution
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] :
    ProjectiveResolution (Rep.trivial Λ G Λ) where
  complex := restrictComplex S P
  π := restrictπ S P ε

open Classical in
/-- Homology of `(P_•)_G` compared with mathlib group homology of the trivial
`G`-module, via the restricted resolution. -/
noncomputable def homologyIso
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (n : ℕ) :
    (Coinvariants.complex S P).homology n ≅
      groupHomology (Rep.trivial Λ G Λ) n :=
  (homologyFunctor (ModuleCat.{u} Λ) (ComplexShape.down ℕ) n).mapIso
      (coinvariantsTensorComplexIso S P).symm ≪≫
    (groupHomologyIso (Rep.trivial Λ G Λ) n (restrictResolution S P ε)).symm

open Classical in
/-- Mathlib's identification `H_n(G, Λ) ≅ Tor_n^{Λ[G]}(Λ, Λ)`. -/
noncomputable def groupHomology_iso_tor (n : ℕ) :
    groupHomology (Rep.trivial Λ G Λ) n ≅
      ((Rep.Tor Λ G n).obj (Rep.trivial Λ G Λ)).obj (Rep.trivial Λ G Λ) :=
  groupHomologyIsoTor (Rep.trivial Λ G Λ) n

open Classical in
/-- The homology of `(P_•)_G` compared with `Tor_n^{Λ[G]}(Λ, Λ)`. -/
noncomputable def homologyIso_tor
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Λ[Γ]))).obj (trivialModule Λ Γ))
    [QuasiIso ε] (n : ℕ) :
    (Coinvariants.complex S P).homology n ≅
      ((Rep.Tor Λ G n).obj (Rep.trivial Λ G Λ)).obj (Rep.trivial Λ G Λ) :=
  homologyIso S P ε n ≪≫ groupHomology_iso_tor n

end LinearMap.FiniteProjective
