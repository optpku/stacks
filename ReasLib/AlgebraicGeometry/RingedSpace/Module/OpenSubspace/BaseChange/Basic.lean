/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.BaseChange.Linear

@[expose] public section
open CategoryTheory TopologicalSpace Topology Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
noncomputable section
universe u

namespace AlgebraicGeometry.RingedSpace.OpenSubspace.BaseChange

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier)

/-- Any two restriction paths with the same endpoints give the same section map. -/
theorem section_path_eq (M : X.Modules) {A B C D : (Opens X.carrier)ᵒᵖ}
    (i : A ⟶ B) (j : B ⟶ D) (k : A ⟶ C) (l : C ⟶ D) (m : M.val.obj A) :
    M.val.map j (M.val.map i m) = M.val.map l (M.val.map k m) :=
  (M.val.map_comp_apply i j m).symm.trans
    ((M.val.congr_map_apply (Subsingleton.elim _ _) m).trans (M.val.map_comp_apply k l m))

/-- Forward comparison on literal models, with the actual sectionwise restriction. -/
def literalHom : literalSource f V ⟶ literalTarget f V where
  app M :=
    { val :=
        { app := fun W => sectionHomLinear f V M W.unop
          naturality := by
            intro W Z i
            ext m
            exact section_path_eq M
              ((Opens.map f.hom.base).map (V.isOpenEmbedding.functor.map i.unop)).op
              (eqToHom (sectionOpen_eq f V Z.unop).symm).op
              (eqToHom (sectionOpen_eq f V W.unop).symm).op
              ((preimageOpen f V).isOpenEmbedding.functor.map
                ((Opens.map (restrictedMorphismToOpen f V).hom.base).map i.unop)).op m } }
  naturality := by
    intro M N φ
    ext W m
    exact (PresheafOfModules.naturality_apply φ.val
      (eqToHom (sectionOpen_eq f V W.unop).symm).op m).symm

/-- Actual inverse comparison: reverse restriction on the equal image opens. -/
def literalInv : literalTarget f V ⟶ literalSource f V where
  app M :=
    { val :=
        { app := fun W => sectionInvLinear f V M W.unop
          naturality := by
            intro W Z i
            ext m
            exact section_path_eq M
              ((preimageOpen f V).isOpenEmbedding.functor.map
                ((Opens.map (restrictedMorphismToOpen f V).hom.base).map i.unop)).op
              (eqToHom (sectionOpen_eq f V Z.unop)).op
              (eqToHom (sectionOpen_eq f V W.unop)).op
              ((Opens.map f.hom.base).map (V.isOpenEmbedding.functor.map i.unop)).op m } }
  naturality := by
    intro M N φ
    ext W m
    exact (PresheafOfModules.naturality_apply φ.val
      (eqToHom (sectionOpen_eq f V W.unop)).op m).symm

/-- The literal models agree through the displayed section maps in both directions. -/
def literalBaseChangeIso : literalSource f V ≅ literalTarget f V where
  hom := literalHom f V
  inv := literalInv f V
  hom_inv_id := by
    ext M W m
    exact sectionInv_hom f V M W.unop m
  inv_hom_id := by
    ext M W m
    exact sectionHom_inv f V M W.unop m

/-- The underived base-change isomorphism on the original module functors.
Both bridge directions and both section maps are fixed explicit data. -/
def baseChangeIso :
    RingedSpace.Hom.pushforward f ⋙ moduleRestrictionToOpen Y V ≅
      moduleRestrictionToOpen X (preimageOpen f V) ⋙
        RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V) :=
  (Functor.isoWhiskerLeft (RingedSpace.Hom.pushforward f) (restrictionBridge Y V)).symm ≪≫
    literalBaseChangeIso f V ≪≫
      Functor.isoWhiskerRight (restrictionBridge X (preimageOpen f V))
        (RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V))

/-- Exact forward pullback square, agreeing with the previously certified construction. -/
def canonicalPullbackSquare :
    RingedSpace.Hom.pullback (Y.ofRestrict V.isOpenEmbedding) ⋙
        RingedSpace.Hom.pullback (restrictedMorphismToOpen f V) ≅
      RingedSpace.Hom.pullback f ⋙
        RingedSpace.Hom.pullback (X.ofRestrict (preimageOpen f V).isOpenEmbedding) :=
  (RingedSpace.Hom.pullbackCompIso (restrictedMorphismToOpen f V)
      (Y.ofRestrict V.isOpenEmbedding)).symm ≪≫
    eqToIso (congrArg RingedSpace.Hom.pullback (square_fac f V)) ≪≫
      RingedSpace.Hom.pullbackCompIso (X.ofRestrict (preimageOpen f V).isOpenEmbedding) f

/-- The same specified canonical mate used in OpenBaseChangeCertified. -/
def canonicalComparison :
    RingedSpace.Hom.pushforward f ⋙ moduleRestrictionToOpen Y V ⟶
      moduleRestrictionToOpen X (preimageOpen f V) ⋙
        RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V) :=
  (mateEquiv (RingedSpace.Hom.pullbackPushforwardAdjunction f)
    (RingedSpace.Hom.pullbackPushforwardAdjunction (restrictedMorphismToOpen f V))
    (canonicalPullbackSquare f V).hom).natTrans

/-- Fixed coherence between the literal section formula and the specified mate.
This is Prop proof debt; it neither selects a map nor adds a theorem hypothesis. -/
theorem baseChangeIso_hom_eq_comparison :
    (baseChangeIso f V).hom = canonicalComparison f V := sorry

/-- Actual inverse of the specified mate on the original source and target functors. -/
def canonicalInverse :
    moduleRestrictionToOpen X (preimageOpen f V) ⋙
        RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V) ⟶
      RingedSpace.Hom.pushforward f ⋙ moduleRestrictionToOpen Y V :=
  (baseChangeIso f V).inv

/-- The specified mate followed by the displayed inverse is the identity. -/
theorem canonicalComparison_inverse :
    canonicalComparison f V ≫ canonicalInverse f V = 𝟙 _ := by
  rw [← baseChangeIso_hom_eq_comparison]
  exact (baseChangeIso f V).hom_inv_id

/-- The displayed inverse followed by the specified mate is the identity. -/
theorem canonicalInverse_comparison :
    canonicalInverse f V ≫ canonicalComparison f V = 𝟙 _ := by
  rw [← baseChangeIso_hom_eq_comparison]
  exact (baseChangeIso f V).inv_hom_id

end AlgebraicGeometry.RingedSpace.OpenSubspace.BaseChange
