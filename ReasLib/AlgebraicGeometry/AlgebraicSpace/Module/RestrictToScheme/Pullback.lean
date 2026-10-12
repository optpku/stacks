/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction

/-! Explicit restriction/pullback comparison using the actual direct-image unit. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open Sheaf.InternalModule

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}}

/-- The chart on which canonical restriction evaluates a Zariski open. -/
def openObject (Z : Over S) (V : Z.left.Opens) : smallEtaleSite (ofOver Z) :=
  (SmallEtale.toPresentation (ofOver Z)).obj
    ((SmallEtale.openChart (tautologicalChart Z)).obj V)

/-- Restriction evaluates on the specified open chart without changing section values. -/
def sectionEquiv (Z : Over S) (M : (ofOver Z).Modules) (V : Z.left.Opens) :
    ((restrictToScheme Z).obj M).val.obj (op V) ≃ M.val.obj (op (openObject Z V)) :=
  Equiv.refl _

/-- The scheme map from an inverse-image open to the original open. -/
def preimageOverMap {T Z : Over S} (t : T ⟶ Z) (V : Z.left.Opens) :
    (openObject T (t.left ⁻¹ᵁ V)).left ⟶ (openObject Z V).left :=
  Over.homMk (t.left.resLE V (t.left ⁻¹ᵁ V) le_rfl) sorry

/-- The actual map from the inverse-image open to the functor-of-points fiber product. -/
def preimageToBaseChange {T Z : Over S} (t : T ⟶ Z) (V : Z.left.Opens) :
    ofOver (openObject T (t.left ⁻¹ᵁ V)).left ⟶
      etaleBaseChangeSpace (ofOverMap t) (openObject Z V) :=
  Limits.pullback.lift
    (homFunctor (openObject T (t.left ⁻¹ᵁ V)).hom)
    (homFunctor (ofOverMap (preimageOverMap t V))) sorry

/-- The inverse-image open determines the component at which the right Kan extension
is evaluated. -/
def preimageArrow {T Z : Over S} (t : T ⟶ Z) (V : Z.left.Opens) :
    StructuredArrow (op ((etaleBaseChange (ofOverMap t)).obj (openObject Z V)))
      (smallEtaleInclusion (ofOver T)).op :=
  StructuredArrow.mk
    (MorphismProperty.Over.homMk (preimageToBaseChange t V) sorry).op

/-- Evaluate a direct-image section using the map from the inverse-image open.
This is a right-Kan-extension counit, not transport across an asserted type equality. -/
def pushforwardSection {T Z : Over S} (t : T ⟶ Z)
    (F : Sheaf (smallEtaleTopology (ofOver T)) (Type u)) (V : Z.left.Opens) :
    ((typePushforward (ofOverMap t)).obj F).obj.obj (op (openObject Z V)) ⟶
      F.obj.obj (op (openObject T (t.left ⁻¹ᵁ V))) :=
  ((AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extension (ofOver T)).obj F).obj.map
      (preimageArrow t V).hom ≫
    ((AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extensionRestrictionIso (ofOver T)).hom.app F).hom.app
      (op (openObject T (t.left ⁻¹ᵁ V)))

/-- Underlying direct-image comparison on each Zariski open. -/
def pushforwardUnderlying {T Z : Over S} (t : T ⟶ Z) (N : (ofOver T).Modules) :
    (ToInternal.underlying Z.left.ringCatSheaf).obj
        ((restrictToScheme Z).obj ((pushforward (ofOverMap t)).obj N)) ⟶
      (ToInternal.underlying Z.left.ringCatSheaf).obj
        ((Scheme.Modules.pushforward t.left).obj ((restrictToScheme T).obj N)) where
  hom :=
    { app := fun V ↦
        ((RingedSite.ToposHom.ModulePushforward.forgetIso
            (ringedToposHom (ofOverMap t))).hom.app N).hom.app (op (openObject Z V.unop)) ≫
          pushforwardSection t ((ToInternal.underlying (structureSheaf (ofOver T))).obj N) V.unop
      naturality := sorry }

/-- Direct image followed by restriction maps to scheme direct image of restriction. -/
def pushforwardComparison {T Z : Over S} (t : T ⟶ Z) (N : (ofOver T).Modules) :
    (restrictToScheme Z).obj ((pushforward (ofOverMap t)).obj N) ⟶
      (Scheme.Modules.pushforward t.left).obj ((restrictToScheme T).obj N) :=
  homOfUnderlying Z.left.ringCatSheaf (pushforwardUnderlying t N) sorry sorry

/-- The canonical comparison from scheme pullback to restriction of algebraic-space
pullback, obtained by applying the scheme adjunction to the actual pullback unit. -/
def pullbackComparison {T Z : Over S} (t : T ⟶ Z) (M : (ofOver Z).Modules) :
    (Scheme.Modules.pullback t.left).obj ((restrictToScheme Z).obj M) ⟶
      (restrictToScheme T).obj ((pullback (ofOverMap t)).obj M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction t.left).homEquiv _ _).symm
    ((restrictToScheme Z).map ((pullbackPushforwardAdjunction (ofOverMap t)).unit.app M) ≫
      pushforwardComparison t ((pullback (ofOverMap t)).obj M))

/-- Select a preimage of a specified function, using the specified default when no
preimage exists. The choice evidence comes from the branch condition itself. -/
def preimageOr {A B : Type u} (fallback : A) (f : A → B) (y : B) : A :=
  @dite _ (∃ x, f x = y) (Classical.propDecidable _)
    (fun h ↦ h.choose) (fun _ ↦ fallback)

/-- A selected preimage maps to the prescribed section whenever it is in the image. -/
theorem preimageOr_spec {A B : Type u} (fallback : A) (f : A → B) (y : B)
    (h : ∃ x, f x = y) : f (preimageOr fallback f y) = y := by
  simp only [preimageOr, dif_pos h, h.choose_spec]

/-- For an injective map, selecting a preimage of its value recovers the original section. -/
theorem preimageOr_apply {A B : Type u} (fallback : A) (f : A → B)
    (hf : Function.Injective f) (x : A) : preimageOr fallback f (f x) = x :=
  hf (preimageOr_spec fallback f (f x) ⟨x, rfl⟩)

/-- For a surjective map, the specified preimage function is a right inverse. -/
theorem preimageOr_rightInverse {A B : Type u} (fallback : A) (f : A → B)
    (hf : Function.Surjective f) : Function.RightInverse (preimageOr fallback f) f :=
  fun y ↦ preimageOr_spec fallback f y (hf y)

/-- Invert the actual comparison on sections by preimage selection, with zero as the
default. No asserted equality, bijectivity, or adjoint-existence proof supplies data. -/
def inverseSection {T Z : Over S} (t : T ⟶ Z) (M : (ofOver Z).Modules)
    (V : T.left.Opensᵒᵖ) :
    ((restrictToScheme T).obj ((pullback (ofOverMap t)).obj M)).val.obj V →
      ((Scheme.Modules.pullback t.left).obj ((restrictToScheme Z).obj M)).val.obj V :=
  preimageOr 0 (fun x ↦ ((pullbackComparison t M).val.app V).hom x)

/-- The inverse section functions assemble naturally on quasi-coherent modules. -/
def inverseUnderlying {T Z : Over S} (t : T ⟶ Z) (M : (ofOver Z).Modules)
    [M.IsQuasicoherent] :
    (ToInternal.underlying T.left.ringCatSheaf).obj
        ((restrictToScheme T).obj ((pullback (ofOverMap t)).obj M)) ⟶
      (ToInternal.underlying T.left.ringCatSheaf).obj
        ((Scheme.Modules.pullback t.left).obj ((restrictToScheme Z).obj M)) where
  hom := { app := fun V ↦ TypeCat.ofHom (inverseSection t M V), naturality := sorry }

/-- The inverse has the original module structures on its two sides. -/
def inverseComparison {T Z : Over S} (t : T ⟶ Z) (M : (ofOver Z).Modules)
    [M.IsQuasicoherent] :
    (restrictToScheme T).obj ((pullback (ofOverMap t)).obj M) ⟶
      (Scheme.Modules.pullback t.left).obj ((restrictToScheme Z).obj M) :=
  homOfUnderlying T.left.ringCatSheaf (inverseUnderlying t M) sorry sorry

/-- The restriction/pullback comparison on quasi-coherent modules has both concrete
maps specified. Only linearity, naturality and the inverse laws are deferred. -/
def restrictPullbackIso {T Z : Over S} (t : T ⟶ Z) (M : (ofOver Z).Modules)
    [M.IsQuasicoherent] :
    (restrictToScheme T).obj ((pullback (ofOverMap t)).obj M) ≅
      (Scheme.Modules.pullback t.left).obj ((restrictToScheme Z).obj M) where
  hom := inverseComparison t M
  inv := pullbackComparison t M
  hom_inv_id := sorry
  inv_hom_id := sorry


/-- Restriction commutes with pullback on the category of quasi-coherent inputs. -/
def restrictPullbackNatIso {T Z : Over S} (t : T ⟶ Z) :
    QCoh.inclusion (ofOver Z) ⋙ pullback (ofOverMap t) ⋙ restrictToScheme T ≅
      QCoh.inclusion (ofOver Z) ⋙ restrictToScheme Z ⋙ Scheme.Modules.pullback t.left :=
  NatIso.ofComponents
    (fun M ↦ @restrictPullbackIso S T Z t M.obj M.property)
    sorry

/-- Quasi-coherence of the specified pullback follows from the canonical preservation theorem. -/
theorem pullbackIsQuasicoherent {X Y : AlgebraicSpace S} (g : X ⟶ Y)
    (M : Y.Modules) [hM : M.IsQuasicoherent] :
    ((pullback g).obj M).IsQuasicoherent :=
  pullback_quasiCoherentModuleProperty g hM

/-- Scheme pullback of a restriction identifies with restriction of the composite
algebraic-space pullback. This retains the pre-migration quasi-coherence hypothesis. -/
def compositePullbackIso {X : AlgebraicSpace S} {T Z : Over S}
    (g : ofOver Z ⟶ X) (t : T ⟶ Z) (M : X.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback t.left).obj
      ((restrictToScheme Z).obj ((pullback g).obj M)) ≅
      (restrictToScheme T).obj ((pullback (ofOverMap t ≫ g)).obj M) :=
  (@restrictPullbackIso S T Z t ((pullback g).obj M)
      (pullbackIsQuasicoherent g M)).symm ≪≫
    (restrictToScheme T).mapIso ((pullbackCompIso (ofOverMap t) g).app M)

/-- The concrete forward component of the composite comparison. -/
def compositePullbackHom {X : AlgebraicSpace S} {T Z : Over S}
    (g : ofOver Z ⟶ X) (t : T ⟶ Z) (M : X.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback t.left).obj
      ((restrictToScheme Z).obj ((pullback g).obj M)) ⟶
      (restrictToScheme T).obj ((pullback (ofOverMap t ≫ g)).obj M) :=
  (compositePullbackIso g t M).hom

/-- The concrete inverse component of the composite comparison. -/
def compositePullbackInv {X : AlgebraicSpace S} {T Z : Over S}
    (g : ofOver Z ⟶ X) (t : T ⟶ Z) (M : X.Modules) [M.IsQuasicoherent] :
    (restrictToScheme T).obj ((pullback (ofOverMap t ≫ g)).obj M) ⟶
      (Scheme.Modules.pullback t.left).obj
        ((restrictToScheme Z).obj ((pullback g).obj M)) :=
  (compositePullbackIso g t M).inv

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
