/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.OverAbelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallSheafification

/-!
# Structure sheaf and modules on the small étale site of an algebraic space

The structure sheaf assigns to an étale chart its ring of global sections. Module sheaves
are sheaves of modules over this ring sheaf on the small étale topology.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism map of `smallEtaleToScheme X` is the underlying morphism of schemes. -/
theorem smallEtaleToScheme_map {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallEtaleSite X} (f : U ⟶ V) : (smallEtaleToScheme X).map f = f.left.left :=
  rfl

/-- The ring presheaf on the small étale site of `X` with value `Γ(U, 𝒪_U)`. -/
abbrev structurePresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u} :=
  (smallEtaleToScheme X).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- The value of `structurePresheaf X` at `U` is the global-sections ring of the underlying
scheme. -/
theorem structurePresheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (structurePresheaf X).obj (op U) = RingCat.of Γ(U.left.left, ⊤) :=
  rfl

/-- Restriction in `structurePresheaf X` is the map on global sections induced by the
underlying morphism of schemes. -/
theorem structurePresheaf_map {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallEtaleSite X} (g : U ⟶ V) :
    (structurePresheaf X).map g.op =
      RingCat.ofHom ((smallEtaleToScheme X).map g).appTop.hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Global sections satisfy étale descent by the Γ–Spec adjunction. -/
private theorem gamma_isSheaf_etale : Presheaf.IsSheaf Scheme.etaleTopology.{u} Scheme.Γ := by
  have etale_le_fppf : Scheme.etaleTopology ≤ Scheme.fppfTopology :=
    Precoverage.toGrothendieck_mono (Scheme.precoverage_mono (by
      intro Y Z f hf
      letI := hf
      exact ⟨inferInstance, inferInstance⟩))
  letI : Scheme.etaleTopology.Subcanonical := .of_le etale_le_fppf
  intro R
  let e : yoneda.obj (Scheme.Spec.obj (op R)) ≅ Scheme.Γ ⋙ coyoneda.obj (op R) :=
    NatIso.ofComponents (fun V ↦
      ((ΓSpec.adjunction.homEquiv V.unop (op R)).symm.trans (opEquiv _ _)).toIso) (by
        intro V Q f
        ext h
        exact congrArg Quiver.Hom.unop
          (ΓSpec.adjunction.homEquiv_naturality_left_symm f.unop h))
  exact Presieve.isSheaf_iso Scheme.etaleTopology
    e
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

set_option backward.isDefEq.respectTransparency false in
/-- Ring homomorphisms glue pointwise, even when the site is larger than the rings. -/
private theorem ring_isSheaf_of_underlying
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ RingCat.{u}) (h : Presieve.IsSheaf J (P ⋙ forget RingCat.{u})) :
    Presheaf.IsSheaf J P := by
  intro R U T hT x hx
  let elements (r : R) : T.arrows.FamilyOfElements (P ⋙ forget RingCat.{u}) :=
    fun V f hf ↦ (x f hf).hom r
  have compatible (r : R) : (elements r).Compatible := by
    intro V W Z g k f l hf hl e
    exact congrArg (fun m : R ⟶ P.obj (op Z) ↦ m.hom r) (hx g k hf hl e)
  let glue (r : R) := (h T hT).amalgamate (elements r) (compatible r)
  have restrict (r : R) {V : C} (f : V ⟶ U) (hf : T f) :
      (P.map f.op).hom (glue r) = (x f hf).hom r :=
    (h T hT).valid_glue (compatible r) f hf
  let g : R ⟶ P.obj (op U) := RingCat.ofHom
    { toFun := glue
      map_zero' := by
        apply (h T hT).isSeparatedFor.ext
        intro V f hf
        change (P.map f.op).hom (glue 0) = (P.map f.op).hom 0
        rw [restrict 0 f hf, map_zero, map_zero]
      map_one' := by
        apply (h T hT).isSeparatedFor.ext
        intro V f hf
        change (P.map f.op).hom (glue 1) = (P.map f.op).hom 1
        rw [restrict 1 f hf, map_one, map_one]
      map_add' := by
        intro r s
        apply (h T hT).isSeparatedFor.ext
        intro V f hf
        change (P.map f.op).hom (glue (r + s)) =
          (P.map f.op).hom (glue r + glue s)
        rw [restrict (r + s) f hf, map_add, map_add, restrict r f hf, restrict s f hf]
      map_mul' := by
        intro r s
        apply (h T hT).isSeparatedFor.ext
        intro V f hf
        change (P.map f.op).hom (glue (r * s)) =
          (P.map f.op).hom (glue r * glue s)
        rw [restrict (r * s) f hf, map_mul, map_mul, restrict r f hf, restrict s f hf] }
  refine ⟨g, ?_, ?_⟩
  · intro V f hf
    change g ≫ P.map f.op = x f hf
    ext r
    exact restrict r f hf
  · intro k hk
    apply RingCat.hom_ext
    apply RingHom.ext
    intro r
    apply (h T hT).isSeparatedFor.ext
    intro V f hf
    change (P.map f.op).hom (k.hom r) = (P.map f.op).hom (glue r)
    rw [restrict r f hf]
    exact congrArg (fun m : R ⟶ P.obj (op V) ↦ m.hom r) (hk f hf)

/-- The global-sections presheaf on the small étale site of an algebraic space is a sheaf. -/
theorem structurePresheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (smallEtaleTopology X) (structurePresheaf X) := by
  letI := smallEtaleToScheme_isContinuous X
  have commutativeSheaf : Presheaf.IsSheaf (smallEtaleTopology X)
      ((smallEtaleToScheme X).op ⋙ Scheme.Γ.{u}) :=
    (smallEtaleToScheme X).op_comp_isSheaf_of_isSheaf
      (smallEtaleTopology X) Scheme.etaleTopology Scheme.Γ gamma_isSheaf_etale
  letI : Limits.PreservesLimitsOfSize.{u, u + 1} (forget CommRingCat.{u}) :=
    CommRingCat.adj.rightAdjoint_preservesLimits
  have underlyingSheaf := Presheaf.isSheaf_comp_of_isSheaf
    (smallEtaleTopology X) ((smallEtaleToScheme X).op ⋙ Scheme.Γ.{u})
    (forget CommRingCat.{u}) commutativeSheaf
  apply ring_isSheaf_of_underlying
  exact (isSheaf_iff_isSheaf_of_type _ _).mp underlyingSheaf

/-- The structure sheaf `𝒪_X` on the small étale site of an algebraic space. -/
def structureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) RingCat.{u} :=
  ⟨structurePresheaf X, structurePresheaf_isSheaf X⟩

/-- On a scheme étale over `X`, the structure sheaf has value `Γ(U, 𝒪_U)`. -/
theorem structureSheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (structureSheaf X).obj.obj (op U) = RingCat.of Γ(U.left.left, ⊤) :=
  rfl

/-- The category of sheaves of modules on the ringed site `(X_étale, 𝒪_X)`. -/
abbrev Modules {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  SheafOfModules.{u} (structureSheaf X)

/-- The module category of `X` is the category of sheaves of modules over `𝒪_X`. -/
theorem Modules_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Modules X = SheafOfModules.{u} (structureSheaf X) :=
  rfl

/-- Abelian-group-valued sheaf composition exists on the small étale topology of an algebraic
space. -/
instance smallEtaleTopology_hasSheafCompose {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  by infer_instance

/-- Abelian-group-valued weak sheafification exists on the small étale topology of an algebraic
space. -/
instance smallEtaleTopology_hasWeakSheafify_addCommGrp {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u} :=
  PullbackFactory.AdditiveSheafification.additive
    (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)

/-- On the small étale topology of an algebraic space, sheafification equivalences are the
locally bijective morphisms. -/
instance smallEtaleTopology_wEqualsLocallyBijective {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  PullbackFactory.AdditiveSheafification.additiveW
    (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)

/-- Abelian-group-valued sheaf composition exists on every slice of the small étale topology of
an algebraic space. -/
instance smallEtaleTopology_over_hasSheafCompose {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ U : smallEtaleSite X,
      ((smallEtaleTopology X).over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists on every slice of the small étale topology of
an algebraic space. -/
instance smallEtaleTopology_over_hasWeakSheafify {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ U : smallEtaleSite X,
      HasWeakSheafify ((smallEtaleTopology X).over U) AddCommGrpCat.{u} :=
  fun U ↦ smallEtaleOverAbelianSheafification X U

/-- On every slice of the small étale topology of an algebraic space, sheafification
equivalences are the locally bijective morphisms. -/
instance smallEtaleTopology_over_wEqualsLocallyBijective {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ U : smallEtaleSite X,
      ((smallEtaleTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Sheafification of abelian-group-valued presheaves on the small étale site of
an algebraic space is left exact. -/
instance smallEtaleTopology_hasSheafify_addCommGrp {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u} := by
  letI := PullbackFactory.AdditiveSheafification.sheafify_preservesFiniteLimits
    (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)
  exact HasSheafify.mk' (smallEtaleTopology X) AddCommGrpCat.{u}
    (PullbackFactory.AdditiveSheafification.adjunction
      (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X))

end AlgebraicGeometry.AlgebraicSpace
