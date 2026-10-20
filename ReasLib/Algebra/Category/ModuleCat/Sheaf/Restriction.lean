module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence for restriction of scalars of module sheaves

The objectwise restriction comparisons for module presheaves lift through the fully faithful
forgetful functor to module sheaves.  This file owns identity, composition, and morphism-level
composition for arbitrary `RingCat`-valued sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable {R R' : Sheaf J RingCat.{u}}

/-- Restriction of scalars leaves the underlying additive sheaf unchanged. -/
@[stacks 01UP "underlying additive sheaf after restriction",
  stacks 04BP "underlying additive sheaf after restriction"]
noncomputable def restrictScalarsCompToSheaf (alpha : R ⟶ R') :
    restrictScalars.{v} alpha ⋙ toSheaf R ≅ toSheaf R' :=
  Iso.refl _

/-- A morphism of ring sheaves, regarded as a morphism between the underlying additive sheaves
of their unit modules. -/
@[stacks 01UP "underlying additive map of ring sheaves",
  stacks 04BP "underlying additive map of ring sheaves"]
noncomputable def unitUnderlyingMap
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (alpha : R ⟶ R') :
    (toSheaf R).obj (unit R) ⟶ (toSheaf R').obj (unit R') :=
  (sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u})).map alpha

/-- The underlying additive map of a ring-sheaf morphism acts by the original morphism on every
local section. -/
@[simp, stacks 01UP "underlying additive map on sections",
  stacks 04BP "underlying additive map on sections"]
theorem unitUnderlyingMap_app_apply
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (alpha : R ⟶ R') (X : Cᵒᵖ) (x : R.obj.obj X) :
    (unitUnderlyingMap alpha).hom.app X x = alpha.hom.app X x := sorry

end SheafOfModules

namespace SheafOfModules.Restriction

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable {R R' R₀ R₁ R₂ : Sheaf J RingCat.{u}}

/-- Restriction along a sheaf morphism identified with the identity, on one module sheaf. -/
@[stacks 0FKQ "identity restriction on a module sheaf"]
noncomputable def idComponentIso' (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : SheafOfModules.{v} R) :
    M ≅ (SheafOfModules.restrictScalars f).obj M :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.Restriction.idComponentIso' f.hom
      (congrArg (fun p : R ⟶ R ↦ p.hom) hf) M.val)

/-- Identity-restriction components are natural in the module sheaf. -/
@[stacks 0FKQ "identity restriction naturality for module sheaves"]
theorem idComponentIso_naturality (f : R ⟶ R) (hf : f = 𝟙 R)
    {M N : SheafOfModules.{v} R} (g : M ⟶ N) :
    g ≫ (idComponentIso' f hf N).hom =
      (idComponentIso' f hf M).hom ≫ (SheafOfModules.restrictScalars f).map g := sorry

/-- The inverse identity-restriction components are natural in the module sheaf. -/
@[stacks 0FKQ "inverse identity restriction naturality for module sheaves"]
theorem idComponentIso_inv_naturality (f : R ⟶ R) (hf : f = 𝟙 R)
    {M N : SheafOfModules.{v} R} (g : M ⟶ N) :
    (SheafOfModules.restrictScalars f).map g ≫
        (idComponentIso' f hf N).inv =
      (idComponentIso' f hf M).inv ≫ g := sorry

/-- The forward identity-restriction components form a natural transformation. -/
@[stacks 0FKQ "forward identity restriction natural transformation for module sheaves"]
noncomputable def idNatTrans' (f : R ⟶ R) (hf : f = 𝟙 R) :
    (𝟭 (SheafOfModules.{v} R) :
        SheafOfModules.{v} R ⥤ SheafOfModules.{v} R) ⟶
      SheafOfModules.restrictScalars f where
  app M := (idComponentIso' f hf M).hom
  naturality _ _ g := idComponentIso_naturality f hf g

/-- The inverse identity-restriction components form the inverse natural transformation. -/
@[stacks 0FKQ "inverse identity restriction natural transformation for module sheaves"]
noncomputable def idInvNatTrans' (f : R ⟶ R) (hf : f = 𝟙 R) :
    SheafOfModules.restrictScalars f ⟶
      (𝟭 (SheafOfModules.{v} R) :
        SheafOfModules.{v} R ⥤ SheafOfModules.{v} R) where
  app M := (idComponentIso' f hf M).inv
  naturality _ _ g := idComponentIso_inv_naturality f hf g

/-- A component of the forward identity-restriction natural transformation is the objectwise
identity-restriction comparison. -/
@[simp,
  stacks 0FKQ "forward identity restriction natural transformation component for module sheaves"]
theorem idNatTrans'_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : SheafOfModules.{v} R) :
    (idNatTrans' f hf).app M = (idComponentIso' f hf M).hom := sorry

/-- A component of the inverse identity-restriction natural transformation is the inverse
objectwise comparison. -/
@[simp,
  stacks 0FKQ "inverse identity restriction natural transformation component for module sheaves"]
theorem idInvNatTrans'_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : SheafOfModules.{v} R) :
    (idInvNatTrans' f hf).app M = (idComponentIso' f hf M).inv := sorry

/-- The forward identity-restriction natural transformation followed by its inverse is the
identity. -/
@[simp,
  stacks 0FKQ "identity restriction natural transformation forward-inverse law for module sheaves"]
theorem idNatTrans'_hom_inv_id (f : R ⟶ R) (hf : f = 𝟙 R) :
    idNatTrans' f hf ≫ idInvNatTrans' f hf = 𝟙 _ := sorry

/-- The inverse identity-restriction natural transformation followed by its forward map is the
identity. -/
@[simp,
  stacks 0FKQ "identity restriction natural transformation inverse-forward law for module sheaves"]
theorem idNatTrans'_inv_hom_id (f : R ⟶ R) (hf : f = 𝟙 R) :
    idInvNatTrans' f hf ≫ idNatTrans' f hf = 𝟙 _ := sorry

/-- Restriction of module sheaves along a morphism identified with the identity is naturally
isomorphic to the identity functor, oriented from identity to restriction. -/
@[stacks 0FKQ "identity restriction for a specified sheaf map"]
noncomputable def idIso' (f : R ⟶ R) (hf : f = 𝟙 R) :
    (𝟭 (SheafOfModules.{v} R) :
        SheafOfModules.{v} R ⥤ SheafOfModules.{v} R) ≅
      SheafOfModules.restrictScalars f :=
  { hom := idNatTrans' f hf
    inv := idInvNatTrans' f hf
    hom_inv_id := idNatTrans'_hom_inv_id f hf
    inv_hom_id := idNatTrans'_inv_hom_id f hf }

/-- The forward natural transformation of `idIso'` is explicit. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism hom for module sheaves"]
theorem idIso'_hom (f : R ⟶ R) (hf : f = 𝟙 R) :
    (idIso' f hf).hom = idNatTrans' f hf := sorry

/-- The inverse natural transformation of `idIso'` is explicit. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism inverse for module sheaves"]
theorem idIso'_inv (f : R ⟶ R) (hf : f = 𝟙 R) :
    (idIso' f hf).inv = idInvNatTrans' f hf := sorry

/-- A component of `idIso'` is the objectwise identity-restriction comparison. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism component for module sheaves"]
theorem idIso'_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : SheafOfModules.{v} R) :
    (idIso' f hf).app M = idComponentIso' f hf M := sorry

/-- The forward component of `idIso'` is the objectwise comparison map. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism hom component for module sheaves"]
theorem idIso'_hom_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : SheafOfModules.{v} R) :
    (idIso' f hf).hom.app M = (idComponentIso' f hf M).hom := sorry

/-- The inverse component of `idIso'` is the objectwise inverse comparison map. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism inverse component for module sheaves"]
theorem idIso'_inv_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : SheafOfModules.{v} R) :
    (idIso' f hf).inv.app M = (idComponentIso' f hf M).inv := sorry

/-- Restriction of module sheaves along the identity is naturally isomorphic to the identity. -/
@[stacks 0FKQ "identity restriction for module sheaves"]
noncomputable def idIso (R : Sheaf J RingCat.{u}) :
    (𝟭 (SheafOfModules.{v} R) :
        SheafOfModules.{v} R ⥤ SheafOfModules.{v} R) ≅
      SheafOfModules.restrictScalars (𝟙 R) :=
  idIso' (𝟙 R) rfl

/-- Successive restrictions along `f` and `g`, identified with restriction along `gf`, on one
module sheaf. -/
@[stacks 0FKQ "composition restriction on a module sheaf"]
noncomputable def compComponentIso' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : SheafOfModules.{v} R₂) :
    (SheafOfModules.restrictScalars g ⋙
        SheafOfModules.restrictScalars f).obj M ≅
      (SheafOfModules.restrictScalars gf).obj M :=
  (SheafOfModules.fullyFaithfulForget R₀).preimageIso
    (PresheafOfModules.Restriction.compComponentIso'
      f.hom g.hom gf.hom (congrArg (fun p : R₀ ⟶ R₂ ↦ p.hom) hgf) M.val)

/-- Composition-restriction components are natural in the module sheaf. -/
@[stacks 0FKQ "composition restriction naturality for module sheaves"]
theorem compComponentIso_naturality (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g)
    {M N : SheafOfModules.{v} R₂} (h : M ⟶ N) :
    (SheafOfModules.restrictScalars g ⋙
          SheafOfModules.restrictScalars f).map h ≫
        (compComponentIso' f g gf hgf N).hom =
      (compComponentIso' f g gf hgf M).hom ≫
        (SheafOfModules.restrictScalars gf).map h := sorry

/-- The inverse composition-restriction components are natural in the module sheaf. -/
@[stacks 0FKQ "inverse composition restriction naturality for module sheaves"]
theorem compComponentIso_inv_naturality (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g)
    {M N : SheafOfModules.{v} R₂} (h : M ⟶ N) :
    (SheafOfModules.restrictScalars gf).map h ≫
        (compComponentIso' f g gf hgf N).inv =
      (compComponentIso' f g gf hgf M).inv ≫
        (SheafOfModules.restrictScalars g ⋙
          SheafOfModules.restrictScalars f).map h := sorry

/-- The forward composition-restriction components form a natural transformation. -/
@[stacks 0FKQ "forward composition restriction natural transformation for module sheaves"]
noncomputable def compNatTrans' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    SheafOfModules.restrictScalars g ⋙
        SheafOfModules.restrictScalars f ⟶
      SheafOfModules.restrictScalars gf where
  app M := (compComponentIso' f g gf hgf M).hom
  naturality _ _ h := compComponentIso_naturality f g gf hgf h

/-- The inverse composition-restriction components form the inverse natural transformation. -/
@[stacks 0FKQ "inverse composition restriction natural transformation for module sheaves"]
noncomputable def compInvNatTrans' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    SheafOfModules.restrictScalars gf ⟶
      SheafOfModules.restrictScalars g ⋙
        SheafOfModules.restrictScalars f where
  app M := (compComponentIso' f g gf hgf M).inv
  naturality _ _ h := compComponentIso_inv_naturality f g gf hgf h

/-- A component of the forward composition-restriction natural transformation is the objectwise
comparison. -/
@[simp,
  stacks 0FKQ "forward composition restriction natural transformation component for module sheaves"]
theorem compNatTrans'_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : SheafOfModules.{v} R₂) :
    (compNatTrans' f g gf hgf).app M = (compComponentIso' f g gf hgf M).hom := sorry

/-- A component of the inverse composition-restriction natural transformation is the inverse
objectwise comparison. -/
@[simp,
  stacks 0FKQ "inverse composition restriction natural transformation component for module sheaves"]
theorem compInvNatTrans'_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : SheafOfModules.{v} R₂) :
    (compInvNatTrans' f g gf hgf).app M =
      (compComponentIso' f g gf hgf M).inv := sorry

/-- The forward composition-restriction natural transformation followed by its inverse is the
identity. -/
@[simp,
  stacks 0FKQ "module-sheaf composition restriction forward-inverse law"]
theorem compNatTrans'_hom_inv_id (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    compNatTrans' f g gf hgf ≫ compInvNatTrans' f g gf hgf = 𝟙 _ := sorry

/-- The inverse composition-restriction natural transformation followed by its forward map is
the identity. -/
@[simp,
  stacks 0FKQ "module-sheaf composition restriction inverse-forward law"]
theorem compNatTrans'_inv_hom_id (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    compInvNatTrans' f g gf hgf ≫ compNatTrans' f g gf hgf = 𝟙 _ := sorry

/-- Successive restrictions of module sheaves are naturally isomorphic to restriction along a
specified morphism identified with the composite. -/
@[stacks 0FKQ "composition restriction for a specified sheaf map"]
noncomputable def compIso' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    SheafOfModules.restrictScalars g ⋙
        SheafOfModules.restrictScalars f ≅
      SheafOfModules.restrictScalars gf :=
  { hom := compNatTrans' f g gf hgf
    inv := compInvNatTrans' f g gf hgf
    hom_inv_id := compNatTrans'_hom_inv_id f g gf hgf
    inv_hom_id := compNatTrans'_inv_hom_id f g gf hgf }

/-- The forward natural transformation of `compIso'` is explicit. -/
@[simp, stacks 0FKQ "composition restriction natural isomorphism hom for module sheaves"]
theorem compIso'_hom (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    (compIso' f g gf hgf).hom = compNatTrans' f g gf hgf := sorry

/-- The inverse natural transformation of `compIso'` is explicit. -/
@[simp, stacks 0FKQ "composition restriction natural isomorphism inverse for module sheaves"]
theorem compIso'_inv (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    (compIso' f g gf hgf).inv = compInvNatTrans' f g gf hgf := sorry

/-- A component of `compIso'` is the objectwise composition-restriction comparison. -/
@[simp, stacks 0FKQ "composition restriction natural isomorphism component for module sheaves"]
theorem compIso'_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : SheafOfModules.{v} R₂) :
    (compIso' f g gf hgf).app M = compComponentIso' f g gf hgf M := sorry

/-- The forward component of `compIso'` is the objectwise comparison map. -/
@[simp, stacks 0FKQ "composition restriction natural isomorphism hom component for module sheaves"]
theorem compIso'_hom_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : SheafOfModules.{v} R₂) :
    (compIso' f g gf hgf).hom.app M =
      (compComponentIso' f g gf hgf M).hom := sorry

/-- The inverse component of `compIso'` is the objectwise inverse comparison map. -/
@[simp,
  stacks 0FKQ "composition restriction natural isomorphism inverse component for module sheaves"]
theorem compIso'_inv_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : SheafOfModules.{v} R₂) :
    (compIso' f g gf hgf).inv.app M =
      (compComponentIso' f g gf hgf M).inv := sorry

/-- Successive restrictions of module sheaves are naturally isomorphic to restriction along the
composite ring-sheaf morphism. -/
@[stacks 0FKQ "composition restriction for module sheaves"]
noncomputable def compIso (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂) :
    SheafOfModules.restrictScalars g ⋙
        SheafOfModules.restrictScalars f ≅
      SheafOfModules.restrictScalars (f ≫ g) :=
  compIso' f g (f ≫ g) rfl

/-- The unit isomorphism for the equivalence induced by an isomorphism of ring sheaves. -/
noncomputable def isoUnit (e : R ≅ R') :
    (𝟭 (SheafOfModules.{v} R) :
        SheafOfModules.{v} R ⥤ SheafOfModules.{v} R) ≅
      SheafOfModules.restrictScalars e.inv ⋙
        SheafOfModules.restrictScalars e.hom :=
  idIso R ≪≫
    (compIso' e.hom e.inv (𝟙 R) e.hom_inv_id.symm).symm

/-- The counit isomorphism for the equivalence induced by an isomorphism of ring sheaves. -/
noncomputable def isoCounit (e : R ≅ R') :
    SheafOfModules.restrictScalars e.hom ⋙
        SheafOfModules.restrictScalars e.inv ≅
      (𝟭 (SheafOfModules.{v} R') :
        SheafOfModules.{v} R' ⥤ SheafOfModules.{v} R') :=
  compIso' e.inv e.hom (𝟙 R') e.inv_hom_id.symm ≪≫
    (idIso R').symm

/-- The unit and counit for restriction along inverse ring-sheaf isomorphisms satisfy the
triangle identity. -/
theorem isoTriangle (e : R ≅ R') (M : SheafOfModules.{v} R) :
    (SheafOfModules.restrictScalars e.inv).map ((isoUnit e).hom.app M) ≫
        (isoCounit e).hom.app ((SheafOfModules.restrictScalars e.inv).obj M) =
      𝟙 ((SheafOfModules.restrictScalars e.inv).obj M) := sorry

/-- Restriction of scalars along the inverse directions of an isomorphism of ring sheaves gives
an equivalence of their categories of module sheaves. -/
noncomputable def equivalenceOfIso (e : R ≅ R') :
    SheafOfModules.{v} R ≌ SheafOfModules.{v} R' where
  functor := SheafOfModules.restrictScalars e.inv
  inverse := SheafOfModules.restrictScalars e.hom
  unitIso := isoUnit e
  counitIso := isoCounit e
  functor_unitIso_comp := isoTriangle e

/-- Compose module-sheaf morphisms over two changes of rings whose specified target map is their
composite. -/
@[stacks 0FKQ "composition of module-sheaf maps over a specified ring map"]
noncomputable def homComp' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g)
    {M₀ : SheafOfModules.{v} R₀} {M₁ : SheafOfModules.{v} R₁}
    {M₂ : SheafOfModules.{v} R₂}
    (alpha : M₀ ⟶ (SheafOfModules.restrictScalars f).obj M₁)
    (beta : M₁ ⟶ (SheafOfModules.restrictScalars g).obj M₂) :
    M₀ ⟶ (SheafOfModules.restrictScalars gf).obj M₂ :=
  alpha ≫ (SheafOfModules.restrictScalars f).map beta ≫
    (compIso' f g gf hgf).hom.app M₂

/-- Compose module-sheaf morphisms over two successive changes of rings. -/
@[stacks 0FKQ "composition of module-sheaf maps over ring changes"]
noncomputable def homComp (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    {M₀ : SheafOfModules.{v} R₀} {M₁ : SheafOfModules.{v} R₁}
    {M₂ : SheafOfModules.{v} R₂}
    (alpha : M₀ ⟶ (SheafOfModules.restrictScalars f).obj M₁)
    (beta : M₁ ⟶ (SheafOfModules.restrictScalars g).obj M₂) :
    M₀ ⟶ (SheafOfModules.restrictScalars (f ≫ g)).obj M₂ :=
  homComp' f g (f ≫ g) rfl alpha beta



end SheafOfModules.Restriction

