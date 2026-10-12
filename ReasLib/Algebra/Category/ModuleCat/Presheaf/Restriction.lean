/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence for restriction of scalars of module presheaves

Restriction of scalars along an identity morphism is naturally isomorphic to the identity, and
successive restrictions are naturally isomorphic to restriction along the composite.  These
comparisons are defined for arbitrary `RingCat`-valued presheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace PresheafOfModules.Restriction

variable {C : Type u'} [Category.{v'} C]
variable {R R₀ R₁ R₂ : Cᵒᵖ ⥤ RingCat.{u}}

/-- The objectwise identity-restriction isomorphism for a ring-presheaf endomorphism identified
with the identity. -/
@[stacks 0FKQ "identity restriction on presheaf sections"]
noncomputable def idComponentApp' (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : PresheafOfModules.{v} R) (X : Cᵒᵖ) :
    M.obj X ≅ ((PresheafOfModules.restrictScalars f).obj M).obj X :=
  (ModuleCat.restrictScalarsId'App (f.app X).hom
    (congrArg (fun p : R ⟶ R ↦ (p.app X).hom) hf) (M.obj X)).symm

/-- The objectwise identity-restriction isomorphisms commute with restriction in the indexing
category. -/
@[stacks 0FKQ "identity restriction naturality on presheaf sections"]
theorem idComponentApp_naturality (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (p : X ⟶ Y) :
    M.map p ≫
        (ModuleCat.restrictScalars (R.map p).hom).map
          (idComponentApp' f hf M Y).hom =
      (idComponentApp' f hf M X).hom ≫
        ((PresheafOfModules.restrictScalars f).obj M).map p := sorry

/-- The identity-restriction isomorphism on a fixed module presheaf. -/
@[stacks 0FKQ "identity restriction on a module presheaf"]
noncomputable def idComponentIso' (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : PresheafOfModules.{v} R) :
    M ≅ (PresheafOfModules.restrictScalars f).obj M :=
  PresheafOfModules.isoMk (idComponentApp' f hf M)
    (fun _ _ p ↦ idComponentApp_naturality f hf M p)

/-- The identity-restriction component isomorphisms are natural in the module presheaf. -/
@[stacks 0FKQ "identity restriction naturality for module presheaves"]
theorem idComponentIso_naturality (f : R ⟶ R) (hf : f = 𝟙 R)
    {M N : PresheafOfModules.{v} R} (g : M ⟶ N) :
    g ≫ (idComponentIso' f hf N).hom =
      (idComponentIso' f hf M).hom ≫
        (PresheafOfModules.restrictScalars f).map g := sorry

/-- The inverse identity-restriction components are natural in the module presheaf. -/
@[stacks 0FKQ "inverse identity restriction naturality for module presheaves"]
theorem idComponentIso_inv_naturality (f : R ⟶ R) (hf : f = 𝟙 R)
    {M N : PresheafOfModules.{v} R} (g : M ⟶ N) :
    (PresheafOfModules.restrictScalars f).map g ≫
        (idComponentIso' f hf N).inv =
      (idComponentIso' f hf M).inv ≫ g := sorry

/-- The forward identity-restriction components form a natural transformation. -/
@[stacks 0FKQ "forward identity restriction natural transformation"]
noncomputable def idNatTrans' (f : R ⟶ R) (hf : f = 𝟙 R) :
    (𝟭 (PresheafOfModules.{v} R) :
        PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} R) ⟶
      PresheafOfModules.restrictScalars f where
  app M := idComponentIso' f hf M |>.hom
  naturality _ _ g := idComponentIso_naturality f hf g

/-- The inverse identity-restriction components form the inverse natural transformation. -/
@[stacks 0FKQ "inverse identity restriction natural transformation"]
noncomputable def idInvNatTrans' (f : R ⟶ R) (hf : f = 𝟙 R) :
    PresheafOfModules.restrictScalars f ⟶
      (𝟭 (PresheafOfModules.{v} R) :
        PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} R) where
  app M := idComponentIso' f hf M |>.inv
  naturality _ _ g := idComponentIso_inv_naturality f hf g

/-- A component of the forward identity-restriction natural transformation is the objectwise
identity-restriction comparison. -/
@[simp, stacks 0FKQ "forward identity restriction natural transformation component"]
theorem idNatTrans'_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : PresheafOfModules.{v} R) :
    (idNatTrans' f hf).app M = (idComponentIso' f hf M).hom := sorry

/-- A component of the inverse identity-restriction natural transformation is the inverse
objectwise comparison. -/
@[simp, stacks 0FKQ "inverse identity restriction natural transformation component"]
theorem idInvNatTrans'_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : PresheafOfModules.{v} R) :
    (idInvNatTrans' f hf).app M = (idComponentIso' f hf M).inv := sorry

/-- The forward identity-restriction natural transformation followed by its inverse is the
identity. -/
@[simp, stacks 0FKQ "identity restriction natural transformation forward-inverse law"]
theorem idNatTrans'_hom_inv_id (f : R ⟶ R) (hf : f = 𝟙 R) :
    idNatTrans' f hf ≫ idInvNatTrans' f hf = 𝟙 _ := sorry

/-- The inverse identity-restriction natural transformation followed by its forward map is the
identity. -/
@[simp, stacks 0FKQ "identity restriction natural transformation inverse-forward law"]
theorem idNatTrans'_inv_hom_id (f : R ⟶ R) (hf : f = 𝟙 R) :
    idInvNatTrans' f hf ≫ idNatTrans' f hf = 𝟙 _ := sorry

/-- Restriction of module presheaves along a ring-presheaf endomorphism identified with the
identity is naturally isomorphic to the identity, oriented from the identity functor to
restriction. -/
@[stacks 0FKQ "identity restriction for a specified presheaf map"]
noncomputable def idIso' (f : R ⟶ R) (hf : f = 𝟙 R) :
    (𝟭 (PresheafOfModules.{v} R) :
        PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} R) ≅
      PresheafOfModules.restrictScalars f :=
  { hom := idNatTrans' f hf
    inv := idInvNatTrans' f hf
    hom_inv_id := idNatTrans'_hom_inv_id f hf
    inv_hom_id := idNatTrans'_inv_hom_id f hf }

/-- The forward natural transformation of `idIso'` is explicit. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism hom"]
theorem idIso'_hom (f : R ⟶ R) (hf : f = 𝟙 R) :
    (idIso' f hf).hom = idNatTrans' f hf := sorry

/-- The inverse natural transformation of `idIso'` is explicit. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism inverse"]
theorem idIso'_inv (f : R ⟶ R) (hf : f = 𝟙 R) :
    (idIso' f hf).inv = idInvNatTrans' f hf := sorry

/-- A component of `idIso'` is the objectwise identity-restriction comparison. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism component"]
theorem idIso'_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : PresheafOfModules.{v} R) :
    (idIso' f hf).app M = idComponentIso' f hf M := sorry

/-- The forward component of `idIso'` is the objectwise comparison map. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism hom component"]
theorem idIso'_hom_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : PresheafOfModules.{v} R) :
    (idIso' f hf).hom.app M = (idComponentIso' f hf M).hom := sorry

/-- The inverse component of `idIso'` is the objectwise inverse comparison map. -/
@[simp, stacks 0FKQ "identity restriction natural isomorphism inverse component"]
theorem idIso'_inv_app (f : R ⟶ R) (hf : f = 𝟙 R)
    (M : PresheafOfModules.{v} R) :
    (idIso' f hf).inv.app M = (idComponentIso' f hf M).inv := sorry

/-- Restriction of module presheaves along the identity ring-presheaf morphism is naturally
isomorphic to the identity. -/
@[stacks 0FKQ "identity restriction for module presheaves"]
noncomputable def idIso (R : Cᵒᵖ ⥤ RingCat.{u}) :
    (𝟭 (PresheafOfModules.{v} R) :
        PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} R) ≅
      PresheafOfModules.restrictScalars (𝟙 R) :=
  idIso' (𝟙 R) rfl

/-- The objectwise isomorphism from successive restrictions to restriction along a specified
composite ring-presheaf morphism. -/
@[stacks 0FKQ "composition restriction on presheaf sections"]
noncomputable def compComponentApp' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : PresheafOfModules.{v} R₂) (X : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars f).obj
        ((PresheafOfModules.restrictScalars g).obj M)).obj X ≅
      ((PresheafOfModules.restrictScalars gf).obj M).obj X :=
  (ModuleCat.restrictScalarsComp'App (f.app X).hom (g.app X).hom (gf.app X).hom
    (congrArg (fun p : R₀ ⟶ R₂ ↦ (p.app X).hom) hgf) (M.obj X)).symm

/-- The objectwise composition-restriction isomorphisms commute with restriction in the
indexing category. -/
@[stacks 0FKQ "composition restriction naturality on presheaf sections"]
theorem compComponentApp_naturality (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : PresheafOfModules.{v} R₂)
    {X Y : Cᵒᵖ} (p : X ⟶ Y) :
    ((PresheafOfModules.restrictScalars f).obj
          ((PresheafOfModules.restrictScalars g).obj M)).map p ≫
        (ModuleCat.restrictScalars (R₀.map p).hom).map
          (compComponentApp' f g gf hgf M Y).hom =
      (compComponentApp' f g gf hgf M X).hom ≫
        ((PresheafOfModules.restrictScalars gf).obj M).map p := sorry

/-- The isomorphism from successive restrictions to restriction along a specified composite,
on a fixed module presheaf. -/
@[stacks 0FKQ "composition restriction on a module presheaf"]
noncomputable def compComponentIso' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : PresheafOfModules.{v} R₂) :
    (PresheafOfModules.restrictScalars g ⋙
        PresheafOfModules.restrictScalars f).obj M ≅
      (PresheafOfModules.restrictScalars gf).obj M :=
  PresheafOfModules.isoMk (compComponentApp' f g gf hgf M)
    (fun _ _ p ↦ compComponentApp_naturality f g gf hgf M p)

/-- The composition-restriction component isomorphisms are natural in the module presheaf. -/
@[stacks 0FKQ "composition restriction naturality for module presheaves"]
theorem compComponentIso_naturality (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g)
    {M N : PresheafOfModules.{v} R₂} (h : M ⟶ N) :
    (PresheafOfModules.restrictScalars g ⋙
          PresheafOfModules.restrictScalars f).map h ≫
        (compComponentIso' f g gf hgf N).hom =
        (compComponentIso' f g gf hgf M).hom ≫
        (PresheafOfModules.restrictScalars gf).map h := sorry

/-- The inverse composition-restriction components are natural in the module presheaf. -/
@[stacks 0FKQ "inverse composition restriction naturality for module presheaves"]
theorem compComponentIso_inv_naturality (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g)
    {M N : PresheafOfModules.{v} R₂} (h : M ⟶ N) :
    (PresheafOfModules.restrictScalars gf).map h ≫
        (compComponentIso' f g gf hgf N).inv =
      (compComponentIso' f g gf hgf M).inv ≫
        (PresheafOfModules.restrictScalars g ⋙
          PresheafOfModules.restrictScalars f).map h := sorry

/-- The forward composition-restriction components form a natural transformation. -/
@[stacks 0FKQ "forward composition restriction natural transformation"]
noncomputable def compNatTrans' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    PresheafOfModules.restrictScalars g ⋙
        PresheafOfModules.restrictScalars f ⟶
      PresheafOfModules.restrictScalars gf where
  app M := (compComponentIso' f g gf hgf M).hom
  naturality _ _ h := compComponentIso_naturality f g gf hgf h

/-- The inverse composition-restriction components form the inverse natural transformation. -/
@[stacks 0FKQ "inverse composition restriction natural transformation"]
noncomputable def compInvNatTrans' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    PresheafOfModules.restrictScalars gf ⟶
      PresheafOfModules.restrictScalars g ⋙
        PresheafOfModules.restrictScalars f where
  app M := (compComponentIso' f g gf hgf M).inv
  naturality _ _ h := compComponentIso_inv_naturality f g gf hgf h

/-- A component of the forward composition-restriction natural transformation is the objectwise
comparison. -/
@[simp, stacks 0FKQ "forward composition restriction natural transformation component"]
theorem compNatTrans'_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : PresheafOfModules.{v} R₂) :
    (compNatTrans' f g gf hgf).app M = (compComponentIso' f g gf hgf M).hom := sorry

/-- A component of the inverse composition-restriction natural transformation is the inverse
objectwise comparison. -/
@[simp, stacks 0FKQ "inverse composition restriction natural transformation component"]
theorem compInvNatTrans'_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : PresheafOfModules.{v} R₂) :
    (compInvNatTrans' f g gf hgf).app M = (compComponentIso' f g gf hgf M).inv := sorry

/-- The forward composition-restriction natural transformation followed by its inverse is the
identity. -/
@[simp, stacks 0FKQ "composition restriction natural transformation forward-inverse law"]
theorem compNatTrans'_hom_inv_id (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    compNatTrans' f g gf hgf ≫ compInvNatTrans' f g gf hgf = 𝟙 _ := sorry

/-- The inverse composition-restriction natural transformation followed by its forward map is
the identity. -/
@[simp, stacks 0FKQ "composition restriction natural transformation inverse-forward law"]
theorem compNatTrans'_inv_hom_id (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    compInvNatTrans' f g gf hgf ≫ compNatTrans' f g gf hgf = 𝟙 _ := sorry

/-- Successive restrictions of module presheaves are naturally isomorphic to restriction along
a specified morphism identified with the composite. -/
@[stacks 0FKQ "composition restriction for a specified presheaf map"]
noncomputable def compIso' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    PresheafOfModules.restrictScalars g ⋙
        PresheafOfModules.restrictScalars f ≅
      PresheafOfModules.restrictScalars gf :=
  { hom := compNatTrans' f g gf hgf
    inv := compInvNatTrans' f g gf hgf
    hom_inv_id := compNatTrans'_hom_inv_id f g gf hgf
    inv_hom_id := compNatTrans'_inv_hom_id f g gf hgf }

/-- The forward natural transformation of `compIso'` is explicit. -/
@[simp, stacks 0FKQ "composition restriction natural isomorphism hom"]
theorem compIso'_hom (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    (compIso' f g gf hgf).hom = compNatTrans' f g gf hgf := sorry

/-- The inverse natural transformation of `compIso'` is explicit. -/
@[simp, stacks 0FKQ "composition restriction natural isomorphism inverse"]
theorem compIso'_inv (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) :
    (compIso' f g gf hgf).inv = compInvNatTrans' f g gf hgf := sorry

/-- A component of `compIso'` is the objectwise composition-restriction comparison. -/
@[simp, stacks 0FKQ "composition restriction natural isomorphism component"]
theorem compIso'_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : PresheafOfModules.{v} R₂) :
    (compIso' f g gf hgf).app M = compComponentIso' f g gf hgf M := sorry

/-- The forward component of `compIso'` is the objectwise comparison map. -/
@[simp, stacks 0FKQ "composition restriction natural isomorphism hom component"]
theorem compIso'_hom_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : PresheafOfModules.{v} R₂) :
    (compIso' f g gf hgf).hom.app M =
      (compComponentIso' f g gf hgf M).hom := sorry

/-- The inverse component of `compIso'` is the objectwise inverse comparison map. -/
@[simp, stacks 0FKQ "composition restriction natural isomorphism inverse component"]
theorem compIso'_inv_app (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g) (M : PresheafOfModules.{v} R₂) :
    (compIso' f g gf hgf).inv.app M =
      (compComponentIso' f g gf hgf M).inv := sorry

/-- Successive restrictions of module presheaves are naturally isomorphic to restriction along
the composite ring-presheaf morphism. -/
@[stacks 0FKQ "composition restriction for module presheaves"]
noncomputable def compIso (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂) :
    PresheafOfModules.restrictScalars g ⋙
        PresheafOfModules.restrictScalars f ≅
      PresheafOfModules.restrictScalars (f ≫ g) :=
  compIso' f g (f ≫ g) rfl

/-- Compose module-presheaf morphisms over two ring-presheaf changes whose specified target map
is identified with their composite. -/
@[stacks 0FKQ "composition of module-presheaf maps over a specified ring map"]
noncomputable def homComp' (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    (gf : R₀ ⟶ R₂) (hgf : gf = f ≫ g)
    {M₀ : PresheafOfModules.{v} R₀} {M₁ : PresheafOfModules.{v} R₁}
    {M₂ : PresheafOfModules.{v} R₂}
    (alpha : M₀ ⟶ (PresheafOfModules.restrictScalars f).obj M₁)
    (beta : M₁ ⟶ (PresheafOfModules.restrictScalars g).obj M₂) :
    M₀ ⟶ (PresheafOfModules.restrictScalars gf).obj M₂ :=
  alpha ≫ (PresheafOfModules.restrictScalars f).map beta ≫
    (compIso' f g gf hgf).hom.app M₂

/-- Compose module-presheaf morphisms over two successive ring-presheaf changes. -/
@[stacks 0FKQ "composition of module-presheaf maps over ring changes"]
noncomputable def homComp (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂)
    {M₀ : PresheafOfModules.{v} R₀} {M₁ : PresheafOfModules.{v} R₁}
    {M₂ : PresheafOfModules.{v} R₂}
    (alpha : M₀ ⟶ (PresheafOfModules.restrictScalars f).obj M₁)
    (beta : M₁ ⟶ (PresheafOfModules.restrictScalars g).obj M₂) :
    M₀ ⟶ (PresheafOfModules.restrictScalars (f ≫ g)).obj M₂ :=
  homComp' f g (f ≫ g) rfl alpha beta



end PresheafOfModules.Restriction
