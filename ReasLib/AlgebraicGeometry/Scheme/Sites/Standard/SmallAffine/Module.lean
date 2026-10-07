module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.SmallAffine
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Modules on the small affine Zariski and étale sites

This module defines the structure sheaves and the restriction and associated-module functors used
to compare quasi-coherent modules on a scheme with modules on its small affine sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf

noncomputable section

universe u

namespace AlgebraicGeometry.SmallStandardTopology.Affine

/-- The commutative global-functions presheaf on the selected small affine site. -/
def commStructurePresheaf (τ : SmallStandardTopology) (S : Scheme.{u}) :
    (site τ S)ᵒᵖ ⥤ CommRingCat.{u} :=
  (toOver τ S).op ⋙ (Over.forget S).op ⋙ Scheme.Γ

/-- The affine commutative structure presheaf is the global-functions presheaf of the canonical
functor to `Over S`. -/
theorem commStructurePresheaf_spec (τ : SmallStandardTopology) (S : Scheme.{u}) :
    commStructurePresheaf τ S =
      (toOver τ S).op ⋙ (Over.forget S).op ⋙ Scheme.Γ := sorry

/-- The underlying ring-valued structure presheaf on the selected small affine site. -/
abbrev structurePresheaf (τ : SmallStandardTopology) (S : Scheme.{u}) :
    (site τ S)ᵒᵖ ⥤ RingCat.{u} :=
  ringPresheafOfComm (commStructurePresheaf τ S)

/-- The affine ring presheaf is obtained by forgetting commutativity. -/
theorem structurePresheaf_spec (τ : SmallStandardTopology) (S : Scheme.{u}) :
    structurePresheaf τ S = ringPresheafOfComm (commStructurePresheaf τ S) := sorry

/-- The affine global-functions presheaf satisfies the sheaf condition. -/
theorem structurePresheaf_isSheaf (τ : SmallStandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (topology τ S) (structurePresheaf τ S) := sorry

/-- The ring-valued structure sheaf on the selected small affine site. -/
noncomputable def structureSheaf (τ : SmallStandardTopology) (S : Scheme.{u}) :
    Sheaf (topology τ S) RingCat.{u} :=
  ⟨structurePresheaf τ S, structurePresheaf_isSheaf τ S⟩

/-- The underlying presheaf of the affine structure sheaf is the affine global-functions
presheaf. -/
theorem structureSheaf_obj (τ : SmallStandardTopology) (S : Scheme.{u}) :
    (structureSheaf τ S).obj = structurePresheaf τ S := sorry

/-- The restricted full-small-site structure sheaf agrees with the affine structure sheaf. -/
theorem structureSheaf_eq_restriction (τ : SmallStandardTopology) (S : Scheme.{u}) :
    structureSheaf τ S =
      ((inclusion τ S).sheafPushforwardContinuous RingCat.{u}
        (topology τ S) (τ.topology S)).obj
          (Scheme.AssociatedModule.smallStructureSheaf τ S) := sorry

/-- The canonical structure-ring map used to restrict module sheaves to the selected affine
site. Its underlying presheaf map is the identity. -/
noncomputable def restrictionStructureMap
    (τ : SmallStandardTopology) (S : Scheme.{u}) :
    structureSheaf τ S ⟶
      ((inclusion τ S).sheafPushforwardContinuous RingCat.{u}
        (topology τ S) (τ.topology S)).obj
          (Scheme.AssociatedModule.smallStructureSheaf τ S) :=
  ⟨𝟙 _⟩

/-- The affine restriction structure map agrees with transport along the canonical
identification of structure sheaves. -/
theorem restrictionStructureMap_def
    (τ : SmallStandardTopology) (S : Scheme.{u}) :
    restrictionStructureMap τ S = eqToHom (structureSheaf_eq_restriction τ S) := sorry

/-- Bundle a module presheaf satisfying the sheaf condition as a module sheaf on the selected
affine site. -/
def asSheaf (τ : SmallStandardTopology) (S : Scheme.{u})
    (F : PresheafOfModules.{u} (structurePresheaf τ S))
    (hF : Presheaf.IsSheaf (topology τ S) F.presheaf) :
    SheafOfModules (structureSheaf τ S) :=
  ⟨F, hF⟩

/-- Forgetting the sheaf proof from `asSheaf` recovers the original module presheaf. -/
theorem asSheaf_val (τ : SmallStandardTopology) (S : Scheme.{u})
    (F : PresheafOfModules.{u} (structurePresheaf τ S))
    (hF : Presheaf.IsSheaf (topology τ S) F.presheaf) :
    (asSheaf τ S F hF).val = F := sorry

/-- Slice sites of the selected affine topology support composition with the ring-to-additive-group
forgetful functor. -/
instance overHasSheafCompose (τ : SmallStandardTopology) (S : Scheme.{u})
    (U : site τ S) :
    ((topology τ S).over U).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) := sorry

/-- Additive sheafification exists on every slice of the selected affine site. -/
instance overHasWeakSheafify (τ : SmallStandardTopology) (S : Scheme.{u})
    (U : site τ S) :
    HasWeakSheafify ((topology τ S).over U) AddCommGrpCat.{u} := sorry

/-- On every affine slice, sheafification equivalences are the locally bijective morphisms. -/
instance overWEqualsLocallyBijective
    (τ : SmallStandardTopology) (S : Scheme.{u}) (U : site τ S) :
    ((topology τ S).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Restriction of module sheaves from the selected full small site to its affine subsite. -/
noncomputable def restriction (τ : SmallStandardTopology) (S : Scheme.{u}) :
    SheafOfModules (Scheme.AssociatedModule.smallStructureSheaf τ S) ⥤
      SheafOfModules (structureSheaf τ S) :=
  SheafOfModules.pushforward (restrictionStructureMap τ S)

/-- The underlying module presheaf of affine restriction is the canonical pushforward along the
affine inclusion. -/
theorem restriction_obj_val (τ : SmallStandardTopology) (S : Scheme.{u})
    (M : SheafOfModules (Scheme.AssociatedModule.smallStructureSheaf τ S)) :
    ((restriction τ S).obj M).val =
      (PresheafOfModules.pushforward (restrictionStructureMap τ S).hom).obj M.val := sorry

/-- Affine restriction preserves quasi-coherence. -/
theorem restriction_mapsTo (τ : SmallStandardTopology) (S : Scheme.{u}) :
    SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf τ S) ≤
      (SheafOfModules.isQuasicoherent (structureSheaf τ S)).inverseImage
        (restriction τ S) := sorry

namespace restriction

/-- The restriction of a quasi-coherent module sheaf is quasi-coherent. -/
instance objIsQuasicoherent (τ : SmallStandardTopology) (S : Scheme.{u})
    (M : (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.smallStructureSheaf τ S)).FullSubcategory) :
    ((restriction τ S).obj M.obj).IsQuasicoherent := sorry

end restriction

/-- Restriction from quasi-coherent modules on the full small site to quasi-coherent modules on
the affine subsite. -/
noncomputable def qcRestriction (τ : SmallStandardTopology) (S : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent
        (Scheme.AssociatedModule.smallStructureSheaf τ S)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent (structureSheaf τ S)).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict (restriction τ S) (restriction_mapsTo τ S)

/-- The object underlying affine quasi-coherent restriction is ordinary module-sheaf
restriction. -/
theorem qcRestriction_obj (τ : SmallStandardTopology) (S : Scheme.{u})
    (M : (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.smallStructureSheaf τ S)).FullSubcategory) :
    ((qcRestriction τ S).obj M).obj = (restriction τ S).obj M.obj := sorry

namespace qcRestriction

/-- Restriction along the dense affine subsite is an equivalence on quasi-coherent module
sheaves. -/
instance isEquivalence (τ : SmallStandardTopology) (S : Scheme.{u}) :
    (qcRestriction τ S).IsEquivalence := sorry

end qcRestriction

/-- The functor associating an affine-site quasi-coherent module to a quasi-coherent module on
`S`. -/
noncomputable def associated (τ : SmallStandardTopology) (S : Scheme.{u}) :
    Scheme.QCoh S ⥤
      (SheafOfModules.isQuasicoherent (structureSheaf τ S)).FullSubcategory :=
  Scheme.AssociatedModule.smallFunctor τ S ⋙ qcRestriction τ S

/-- The affine module associated to `G` is obtained by full-small-site association followed by
affine restriction. -/
theorem associated_obj (τ : SmallStandardTopology) (S : Scheme.{u})
    (G : Scheme.QCoh S) :
    (associated τ S).obj G =
      (qcRestriction τ S).obj
        ((Scheme.AssociatedModule.smallFunctor τ S).obj G) := sorry

namespace associated

/-- The associated affine-module functor is an equivalence. -/
instance isEquivalence (τ : SmallStandardTopology) (S : Scheme.{u}) :
    (associated τ S).IsEquivalence := sorry

end associated

/-- An affine quasi-coherent module has a unique scheme model when it is identified with an
associated module and every other such identification is induced by a unique compatible
isomorphism. -/
def HasUniqueSchemeModel (τ : SmallStandardTopology) (S : Scheme.{u})
    (M : (SheafOfModules.isQuasicoherent
      (structureSheaf τ S)).FullSubcategory) : Prop :=
  ∃ (G : Scheme.QCoh S) (e : (associated τ S).obj G ≅ M),
    ∀ (G' : Scheme.QCoh S) (e' : (associated τ S).obj G' ≅ M),
      ∃! i : G ≅ G', (associated τ S).map i.hom ≫ e'.hom = e.hom

/-- A scheme model consists of an associated-module identification and is unique exactly when
every competing identification is induced by a unique compatible isomorphism. -/
theorem hasUniqueSchemeModel_iff (τ : SmallStandardTopology) (S : Scheme.{u})
    (M : (SheafOfModules.isQuasicoherent
      (structureSheaf τ S)).FullSubcategory) :
    HasUniqueSchemeModel τ S M ↔
      ∃ (G : Scheme.QCoh S) (e : (associated τ S).obj G ≅ M),
        ∀ (G' : Scheme.QCoh S) (e' : (associated τ S).obj G' ≅ M),
          ∃! i : G ≅ G', (associated τ S).map i.hom ≫ e'.hom = e.hom := sorry

end AlgebraicGeometry.SmallStandardTopology.Affine
