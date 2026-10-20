module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Chaotic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Affine.ModulePresheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Affine.RingedTopos

/-!
# Quasi-coherent modules on standard affine sites

This module relates cartesian module presheaves on affine schemes to quasi-coherent modules on
standard affine and big sites and to quasi-coherent modules on the base scheme.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Presheaf

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Affine

/-- The affine structure sheaf before universe lifting. Its underlying presheaf is
`ringPresheaf (commRingPresheaf S)`. -/
noncomputable def unliftedStructureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (topology τ S) RingCat.{u} :=
  ⟨ringPresheaf (commRingPresheaf S), sorry⟩

/-- The underlying presheaf of the unlifted affine structure sheaf is the presheaf of rings of
global functions. -/
theorem unliftedStructureSheaf_obj (τ : StandardTopology) (S : Scheme.{u}) :
    (unliftedStructureSheaf τ S).obj = ringPresheaf (commRingPresheaf S) := sorry

/-- Abelian-group-valued sheaf composition exists on slices of every affine standard site. -/
instance affineHasSheafComposeOver (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : S.AffineOver,
      ((topology τ S).over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u}) := sorry

/-- Abelian-group-valued weak sheafification exists on slices of every affine standard site. -/
instance affineHasWeakSheafifyOver (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : S.AffineOver,
      HasWeakSheafify ((topology τ S).over U) AddCommGrpCat.{u} := sorry

/-- Local bijectivity characterizes sheafification equivalences on slices of every affine
standard site. -/
instance affineWEqualsLocallyBijectiveOver (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : S.AffineOver,
      ((topology τ S).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

namespace ModulePresheaf

/-- Quasi-coherence of an affine module presheaf for the selected standard topology: the
presheaf is a sheaf and its resulting module sheaf is quasi-coherent. -/
def IsQuasicoherentFor {S : Scheme.{u}} (F : ModulePresheaf S)
    (τ : StandardTopology) : Prop :=
  ∃ hF : Presheaf.IsSheaf (topology τ S) F.presheaf,
    (⟨F, hF⟩ : SheafOfModules (unliftedStructureSheaf τ S)).IsQuasicoherent

/-- The affine quasi-coherence predicate records exactly sheafhood and quasi-coherence of the
resulting module sheaf. -/
theorem isQuasicoherentFor_iff {S : Scheme.{u}} (F : ModulePresheaf S)
    (τ : StandardTopology) :
    F.IsQuasicoherentFor τ ↔
      ∃ hF : Presheaf.IsSheaf (topology τ S) F.presheaf,
        (⟨F, hF⟩ : SheafOfModules (unliftedStructureSheaf τ S)).IsQuasicoherent := sorry

end ModulePresheaf

/-- Restriction of a quasi-coherent module on the big `τ`-site to affine schemes, bundled as
a cartesian affine module presheaf. -/
noncomputable def bigRestriction (τ : StandardTopology) (S : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.bigStructureSheaf τ S)).FullSubcategory ⥤
        CartesianModule S where
  obj F :=
    ⟨(PresheafOfModules.pushforward₀ (Scheme.AffineOver.forget S)
      (Scheme.AssociatedModule.bigStructureSheaf τ S).obj).obj F.obj.val, sorry⟩
  map f :=
    ⟨(PresheafOfModules.pushforward₀ (Scheme.AffineOver.forget S)
      (Scheme.AssociatedModule.bigStructureSheaf τ S).obj).map f.hom.val⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying affine presheaf of `bigRestriction` is literal restriction along the affine
inclusion. -/
theorem bigRestriction_obj (τ : StandardTopology) (S : Scheme.{u})
    (F : (SheafOfModules.isQuasicoherent
      (Scheme.AssociatedModule.bigStructureSheaf τ S)).FullSubcategory) :
    ((bigRestriction τ S).obj F).obj =
      (PresheafOfModules.pushforward₀ (Scheme.AffineOver.forget S)
        (Scheme.AssociatedModule.bigStructureSheaf τ S).obj).obj F.obj.val := sorry

/-- Big-site restriction is an equivalence onto cartesian affine module presheaves. -/
instance bigRestriction_isEquivalence (τ : StandardTopology) (S : Scheme.{u}) :
    (bigRestriction τ S).IsEquivalence := sorry

/-- The affine pullback-sections functor associated to quasi-coherent modules on `S`, bundled
as cartesian affine module presheaves. -/
noncomputable def associatedFunctor (S : Scheme.{u}) :
    Scheme.QCoh S ⥤ CartesianModule S where
  obj F :=
    ⟨(Scheme.Modules.pullbackSectionsFunctor (Scheme.AffineOver.forget S)).obj F.obj, sorry⟩
  map f :=
    ⟨(Scheme.Modules.pullbackSectionsFunctor (Scheme.AffineOver.forget S)).map f.hom⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying presheaf of an associated affine module is the pullback-sections
presheaf. -/
theorem associatedFunctor_obj (S : Scheme.{u}) (F : Scheme.QCoh S) :
    ((associatedFunctor S).obj F).obj =
      (Scheme.Modules.pullbackSectionsFunctor (Scheme.AffineOver.forget S)).obj F.obj := sorry

/-- The associated affine-module functor is an equivalence. -/
instance associatedFunctor_isEquivalence (S : Scheme.{u}) :
    (associatedFunctor S).IsEquivalence := sorry

namespace ModulePresheaf

/-- Cartesianness of an affine module presheaf is equivalent to quasi-coherence for any
selected standard topology. -/
theorem isCartesian_iff_isQuasicoherentFor (τ : StandardTopology) (S : Scheme.{u})
    (F : ModulePresheaf S) :
    F.IsCartesian ↔ F.IsQuasicoherentFor τ := sorry

/-- An affine module presheaf is cartesian exactly when it is the restriction of a
quasi-coherent module on the corresponding big standard site. -/
theorem isCartesian_iff_essImage_big (τ : StandardTopology) (S : Scheme.{u})
    (F : ModulePresheaf S) :
    F.IsCartesian ↔
      (bigRestriction τ S ⋙ CartesianModule.inclusion S).essImage F := sorry

/-- An affine module presheaf is cartesian exactly when it belongs to the essential image of
the pullback-sections functor from quasi-coherent modules on the base scheme. -/
theorem isCartesian_iff_essImage_associated (S : Scheme.{u})
    (F : ModulePresheaf S) :
    F.IsCartesian ↔
      (associatedFunctor S ⋙ CartesianModule.inclusion S).essImage F := sorry

/-- An affine module presheaf has a unique scheme model when it is identified with the
pullback-sections presheaf of some quasi-coherent module and every competing identification
comes from a unique compatible isomorphism of quasi-coherent modules. -/
def HasUniqueSchemeModel {S : Scheme.{u}} (F : ModulePresheaf S) : Prop :=
  ∃ (G : Scheme.QCoh S)
      (e : (associatedFunctor S ⋙ CartesianModule.inclusion S).obj G ≅ F),
    ∀ (G' : Scheme.QCoh S)
      (e' : (associatedFunctor S ⋙ CartesianModule.inclusion S).obj G' ≅ F),
      ∃! i : G ≅ G',
        (associatedFunctor S ⋙ CartesianModule.inclusion S).mapIso i ≪≫ e' = e

/-- The unique-scheme-model predicate is the existence of a model and identification such
that every competing model admits a unique compatible isomorphism from the chosen model. -/
theorem hasUniqueSchemeModel_iff {S : Scheme.{u}} (F : ModulePresheaf S) :
    F.HasUniqueSchemeModel ↔
      ∃ (G : Scheme.QCoh S)
          (e : (associatedFunctor S ⋙ CartesianModule.inclusion S).obj G ≅ F),
        ∀ (G' : Scheme.QCoh S)
          (e' : (associatedFunctor S ⋙ CartesianModule.inclusion S).obj G' ≅ F),
          ∃! i : G ≅ G',
            (associatedFunctor S ⋙ CartesianModule.inclusion S).mapIso i ≪≫ e' = e := sorry

/-- An affine module presheaf is cartesian exactly when it has a unique compatible model by a
quasi-coherent module on the base scheme. -/
theorem isCartesian_iff_hasUniqueSchemeModel (S : Scheme.{u})
    (F : ModulePresheaf S) :
    F.IsCartesian ↔ F.HasUniqueSchemeModel := sorry

end ModulePresheaf

end AlgebraicGeometry.StandardTopology.Affine
