module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_14_1

/-!
# Restriction of quasi-coherent modules along a representing algebraic space

If `e : F.toGroupoids ≌ X`, restriction of quasi-coherent modules along the
functor 96.10.2.1 is `ℱ ↦ ℱ|_{F_étale}`, implemented by identity-on-Γ transport
to the ring-valued étale ringed site of Lemma 96.10.1 followed by
`restrictModules`. The specified quasi-inverse is `G ↦ π_F^* G`.

The 96.12.4 commutative-presentation `etaleModules` owner cannot be imported
together with `restrictModules`, so identity-on-Γ transport uses the ring-valued
`etaleRingedSite` of Lemma 96.10.1. Both structure presheaves unfold as
`p.op ⋙ Γ` on the total category of `X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
  CategoryTheory.ObjectProperty Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Unfolding of fppf `𝒪_X` as precomposition with `X.p.op`. -/
def fppfStructurePresheafUnfold (X : GroupoidsOver S) :
    (fppfRingedSite X).structureSheaf.obj ≅
      X.p.op ⋙ (StandardTopology.Big.structureSheaf .fppf S).obj :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S)

/-- Unfolding of the 96.10.1 étale structure presheaf as precomposition with
`X.p.op`. -/
def etaleRingedStructurePresheafUnfold (X : GroupoidsOver S) :
    (etaleRingedSite X).structureSheaf.obj ≅
      X.p.op ⋙ (StandardTopology.Big.structureSheaf .etale S).obj :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      X.etaleTopology (StandardTopology.etale.overTopology S)).app
    (StandardTopology.Big.structureSheaf .etale S)

/-- Identity-on-Γ isomorphism of the fppf and étale structure presheaves of `X`,
as the composite of the two continuous-pushforward unfoldings. The intermediate
functors agree because both big structure presheaves are `Γ` on `Over S`. -/
def fppfToEtaleRingedStructurePresheafIso (X : GroupoidsOver S) :
    (fppfRingedSite X).structureSheaf.obj ≅ (etaleRingedSite X).structureSheaf.obj :=
  fppfStructurePresheafUnfold X ≪≫
    (etaleRingedStructurePresheafUnfold X).symm

/-- `fppfToEtaleRingedStructurePresheafIso` is the composite of the two
continuous-pushforward unfoldings. -/
theorem fppfToEtaleRingedStructurePresheafIso_eq (X : GroupoidsOver S) :
    fppfToEtaleRingedStructurePresheafIso X =
      fppfStructurePresheafUnfold X ≪≫
        (etaleRingedStructurePresheafUnfold X).symm :=
  rfl

/-- Transport of étale `𝒪_X`-modules on the ring-valued étale ringed site back to
fppf `𝒪_X`-modules, by restriction of scalars along
`fppfToEtaleRingedStructurePresheafIso.hom`. -/
def fromEtaleModules (X : GroupoidsOver S) :
    SheafOfModules.{u} (etaleRingedSite X).structureSheaf ⥤
      RingedSite.ModuleCat.{u} (fppfRingedSite X) where
  obj F :=
    { val :=
        (PresheafOfModules.restrictScalars
          (fppfToEtaleRingedStructurePresheafIso X).hom).obj F.val
      isSheaf := sorry }
  map f :=
    { val :=
        (PresheafOfModules.restrictScalars
          (fppfToEtaleRingedStructurePresheafIso X).hom).map f.val }
  map_id := sorry
  map_comp := sorry

/-- The object action of `fromEtaleModules` is restriction of scalars along
`fppfToEtaleRingedStructurePresheafIso.hom`. -/
theorem fromEtaleModules_obj (X : GroupoidsOver S)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    ((fromEtaleModules X).obj F).val =
      (PresheafOfModules.restrictScalars
        (fppfToEtaleRingedStructurePresheafIso X).hom).obj F.val :=
  rfl

/-- Transport of fppf `𝒪_X`-modules to the ring-valued étale ringed site of
Lemma 96.10.1, by restriction of scalars along
`fppfToEtaleRingedStructurePresheafIso.inv`. -/
def toEtaleRingedModules (X : GroupoidsOver S) :
    RingedSite.ModuleCat.{u} (fppfRingedSite X) ⥤
      SheafOfModules.{u} (etaleRingedSite X).structureSheaf where
  obj F :=
    { val :=
        (PresheafOfModules.restrictScalars
          (fppfToEtaleRingedStructurePresheafIso X).inv).obj F.val
      isSheaf := sorry }
  map f :=
    { val :=
        (PresheafOfModules.restrictScalars
          (fppfToEtaleRingedStructurePresheafIso X).inv).map f.val }
  map_id := sorry
  map_comp := sorry

/-- The object action of `toEtaleRingedModules` is restriction of scalars along
`fppfToEtaleRingedStructurePresheafIso.inv`. -/
theorem toEtaleRingedModules_obj (X : GroupoidsOver S)
    (F : RingedSite.ModuleCat.{u} (fppfRingedSite X)) :
    ((toEtaleRingedModules X).obj F).val =
      (PresheafOfModules.restrictScalars
        (fppfToEtaleRingedStructurePresheafIso X).inv).obj F.val :=
  rfl

/-- `fromEtaleModules` followed by `toEtaleRingedModules` is isomorphic to the
identity on étale modules, via the identity on underlying abelian presheaves. -/
def toFromEtaleModulesIso (X : GroupoidsOver S) :
    fromEtaleModules X ⋙ toEtaleRingedModules X ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F =>
      { hom :=
          { val :=
              PresheafOfModules.homMk
                (𝟙 ((toEtaleRingedModules X).obj ((fromEtaleModules X).obj F)).val.presheaf)
                sorry }
        inv :=
          { val :=
              PresheafOfModules.homMk
                (𝟙 F.val.presheaf)
                sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- `toEtaleRingedModules` followed by `fromEtaleModules` is isomorphic to the
identity on fppf modules, via the identity on underlying abelian presheaves. -/
def fromToEtaleModulesIso (X : GroupoidsOver S) :
    toEtaleRingedModules X ⋙ fromEtaleModules X ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F =>
      { hom :=
          { val :=
              PresheafOfModules.homMk
                (𝟙 ((fromEtaleModules X).obj ((toEtaleRingedModules X).obj F)).val.presheaf)
                sorry }
        inv :=
          { val :=
              PresheafOfModules.homMk
                (𝟙 F.val.presheaf)
                sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

variable {F : AlgebraicSpace S} {X : GroupoidsOver S}

/-- Quasi-coherent modules on `X` remain quasi-coherent after identity-on-Γ
transport to the 96.10.1 étale ringed site and restriction along
`restrictModules e`. -/
theorem restrict_le (e : F.toGroupoids ≌ X) :
    quasiCoherentModuleProperty X ≤
      (AlgebraicSpace.quasiCoherentModuleProperty F).inverseImage
        (toEtaleRingedModules X ⋙ restrictModules e) :=
  sorry

/-- Quasi-coherent modules on `F` remain quasi-coherent after pullback along
`π_F` and identity-on-Γ transport back to the fppf ringed site of `X`. -/
theorem piStar_le (e : F.toGroupoids ≌ X) :
    AlgebraicSpace.quasiCoherentModuleProperty F ≤
      (quasiCoherentModuleProperty X).inverseImage
        ((pi F X e).modulePullback.{u} ⋙ fromEtaleModules X) :=
  sorry

namespace QCoh

/-- Restriction of quasi-coherent modules along a representing algebraic space,
as the functor `ℱ ↦ ℱ|_{F_étale}` of 96.10.2.1, after identity-on-Γ reduction
to the étale topology. -/
def restrict (e : F.toGroupoids ≌ X) :
    QCoh X ⥤ AlgebraicSpace.QCoh F :=
  (AlgebraicSpace.quasiCoherentModuleProperty F).lift
    (inclusion X ⋙ toEtaleRingedModules X ⋙ restrictModules e)
    fun ℱ => restrict_le e ℱ.obj ℱ.property

/-- The underlying module sheaf of `QCoh.restrict e` is `restrictModules e`
after identity-on-Γ transport. -/
theorem restrict_obj (e : F.toGroupoids ≌ X) (ℱ : QCoh X) :
    ((restrict e).obj ℱ).obj =
      (restrictModules e).obj ((toEtaleRingedModules X).obj ℱ.obj) :=
  rfl

/-- The specified quasi-inverse of `QCoh.restrict e`, sending `G` to `π_F^* G`
followed by identity-on-Γ transport to fppf quasi-coherent modules on `X`. -/
def piStar (e : F.toGroupoids ≌ X) :
    AlgebraicSpace.QCoh F ⥤ QCoh X :=
  (quasiCoherentModuleProperty X).lift
    (AlgebraicSpace.QCoh.inclusion F ⋙
      (pi F X e).modulePullback.{u} ⋙ fromEtaleModules X)
    fun G => piStar_le e G.obj G.property

/-- The underlying module sheaf of `QCoh.piStar e` is `π_F^*` followed by
`fromEtaleModules`. -/
theorem piStar_obj (e : F.toGroupoids ≌ X) (G : AlgebraicSpace.QCoh F) :
    ((piStar e).obj G).obj =
      (fromEtaleModules X).obj ((pi F X e).modulePullback.{u}.obj G.obj) :=
  rfl

/-- Because `π_F ∘ i_F = id`, the unit of `π_F^* ⊣ π_{F,*}` identifies `G` with
its restriction after pullback, up to identity-on-Γ transport. -/
def restrict_piStarUnit (e : F.toGroupoids ≌ X) (G : AlgebraicSpace.QCoh F) :
    G ⟶ (restrict e).obj ((piStar e).obj G) :=
  homMk
    ((RingedSite.Hom.modulePullbackPushforwardAdjunction.{u} (pi F X e)).unit.app G.obj ≫
      (restrictModules e).map
        ((toFromEtaleModulesIso X).inv.app
          ((pi F X e).modulePullback.{u}.obj G.obj)))

/-- The adjunction counit `(π_F^* (ℱ|_{F_étale})) ⟶ ℱ`, after identity-on-Γ
transport. This map is an isomorphism when `ℱ` is quasi-coherent. -/
def piStar_restrictCounit (e : F.toGroupoids ≌ X) (ℱ : QCoh X) :
    (piStar e).obj ((restrict e).obj ℱ) ⟶ ℱ :=
  homMk
    ((fromEtaleModules X).map
        ((RingedSite.Hom.modulePullbackPushforwardAdjunction.{u}
            (pi F X e)).counit.app ((toEtaleRingedModules X).obj ℱ.obj)) ≫
      (fromToEtaleModulesIso X).hom.app ℱ.obj)

/-- Because `π_F ∘ i_F = id`, the adjunction unit `G ⟶ π_{F,*} π_F^* G` is an
isomorphism. -/
instance modulePullbackPushforward_unit_isIso (e : F.toGroupoids ≌ X)
    (G : AlgebraicSpace.QCoh F) :
    IsIso ((RingedSite.Hom.modulePullbackPushforwardAdjunction.{u}
        (pi F X e)).unit.app G.obj) :=
  sorry

/-- The adjunction counit `π_F^* π_{F,*} ℱ ⟶ ℱ` is an isomorphism on the étale
ringed site after identity-on-Γ transport of a quasi-coherent module. -/
instance modulePullbackPushforward_counit_isIso (e : F.toGroupoids ≌ X)
    (ℱ : QCoh X) :
    IsIso ((RingedSite.Hom.modulePullbackPushforwardAdjunction.{u}
        (pi F X e)).counit.app ((toEtaleRingedModules X).obj ℱ.obj)) :=
  sorry

/-- Inverse of `restrict_piStarUnit`. Because `π_F ∘ i_F = id`, the adjunction
unit `G ⟶ π_{F,*} π_F^* G` is inverted after reversing identity-on-Γ
transport along `toFromEtaleModulesIso`. -/
def restrict_piStarUnitInv (e : F.toGroupoids ≌ X) (G : AlgebraicSpace.QCoh F) :
    (restrict e).obj ((piStar e).obj G) ⟶ G :=
  homMk
    ((restrictModules e).map
        ((toFromEtaleModulesIso X).hom.app
          ((pi F X e).modulePullback.{u}.obj G.obj)) ≫
      (@CategoryTheory.asIso _ _ _ _
          ((RingedSite.Hom.modulePullbackPushforwardAdjunction.{u}
              (pi F X e)).unit.app G.obj)
          (modulePullbackPushforward_unit_isIso e G)).inv)

/-- Inverse of `piStar_restrictCounit`. The adjunction counit
`π_F^* π_{F,*} ℱ ⟶ ℱ` is inverted after reversing identity-on-Γ transport
along `fromToEtaleModulesIso`. -/
def piStar_restrictCounitInv (e : F.toGroupoids ≌ X) (ℱ : QCoh X) :
    ℱ ⟶ (piStar e).obj ((restrict e).obj ℱ) :=
  homMk
    ((fromToEtaleModulesIso X).inv.app ℱ.obj ≫
      (fromEtaleModules X).map
        (@CategoryTheory.asIso _ _ _ _
            ((RingedSite.Hom.modulePullbackPushforwardAdjunction.{u}
                (pi F X e)).counit.app ((toEtaleRingedModules X).obj ℱ.obj))
            (modulePullbackPushforward_counit_isIso e ℱ)).inv)

/-- Specified unit of the quasi-inverse: `id ≅ piStar e ⋙ restrict e`, from
`π_F ∘ i_F = id` so `i_F^* π_F^* G = G`. -/
def restrict_piStarIso (e : F.toGroupoids ≌ X) :
    𝟭 (AlgebraicSpace.QCoh F) ≅ piStar e ⋙ restrict e :=
  NatIso.ofComponents
    (fun G =>
      { hom := restrict_piStarUnit e G
        inv := restrict_piStarUnitInv e G
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Specified counit of the quasi-inverse: `restrict e ⋙ piStar e ≅ id`. -/
def piStar_restrictIso (e : F.toGroupoids ≌ X) :
    restrict e ⋙ piStar e ≅ 𝟭 (QCoh X) :=
  NatIso.ofComponents
    (fun ℱ =>
      { hom := piStar_restrictCounit e ℱ
        inv := piStar_restrictCounitInv e ℱ
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The unit `G ⟶ (restrict e).obj ((piStar e).obj G)` is an isomorphism. -/
instance restrict_piStarUnit_isIso (e : F.toGroupoids ≌ X)
    (G : AlgebraicSpace.QCoh F) :
    IsIso (restrict_piStarUnit e G) :=
  Iso.isIso_hom ((restrict_piStarIso e).app G)

/-- The counit `π_F^* (ℱ|_{F_étale}) ⟶ ℱ` is an isomorphism for quasi-coherent
`ℱ`. -/
instance piStar_restrictCounit_isIso (e : F.toGroupoids ≌ X) (ℱ : QCoh X) :
    IsIso (piStar_restrictCounit e ℱ) :=
  Iso.isIso_hom ((piStar_restrictIso e).app ℱ)

end QCoh

end AlgebraicGeometry.GroupoidsOver
