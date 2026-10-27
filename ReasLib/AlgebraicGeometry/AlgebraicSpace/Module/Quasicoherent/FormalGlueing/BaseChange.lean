/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FormalGlueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-! # Base change of quasi-coherent formal-glueing triples -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

/-- Pullback transports the structural isomorphism of a glueing triple. -/
def pulledBackφ {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    {H : QCoh (closedImmersionComplement i)} {G : QCoh Y}
    (φ : (pullback (restrictToComplement f i)).obj H ≅
      (pullback (closedImmersionComplementι (inverseImageι f i))).obj G) :
    (pullback (restrictToComplement (f' f g) (i' i g))).obj
        ((pullback (complementBaseChange i g)).obj H) ≅
      (pullback (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)))).obj
        ((pullback (toY f g)).obj G) :=
  (QCoh.pullbackCompIso (complementBaseChange i g)
      (restrictToComplement (f' f g) (i' i g))).app H ≪≫
    eqToIso (congrArg (fun h ↦ (pullback h).obj H)
      (overlapBaseChange_comp_restrict f i g).symm) ≪≫
    (QCoh.pullbackCompIso (restrictToComplement f i) (overlapBaseChange f i g)).symm.app H ≪≫
    (pullback (overlapBaseChange f i g)).mapIso φ ≪≫
    (QCoh.pullbackCompIso (closedImmersionComplementι (inverseImageι f i))
      (overlapBaseChange f i g)).app G ≪≫
    eqToIso (congrArg (fun h ↦ (pullback h).obj G) (overlapBaseChange_comp_ι f i g)) ≪≫
    (QCoh.pullbackCompIso (toY f g)
      (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)))).symm.app G

section

variable {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
variable (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]

/-- Pulling back both components and their structural isomorphism gives a glueing triple
over the base-changed spaces. -/
private def baseChangeObj (t : category f i) : category (f' f g) (i' i g) :=
  ⟨(pullback (complementBaseChange i g)).obj t.fst,
    (pullback (toY f g)).obj t.snd, pulledBackφ f i g t.iso⟩

/-- Pullback of compatible component maps respects the transported structural isomorphisms. -/
private theorem baseChange_map_w {t t' : category f i} (α : t ⟶ t') :
    (pullback (restrictToComplement (f' f g) (i' i g))).map
        ((pullback (complementBaseChange i g)).map α.fst) ≫
        (pulledBackφ f i g t'.iso).hom =
      (pulledBackφ f i g t.iso).hom ≫
        (pullback (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)))).map
          ((pullback (toY f g)).map α.snd) :=
  sorry

/-- Pullback of the two component maps defines a morphism of base-changed glueing triples. -/
private def baseChangeMap {t t' : category f i} (α : t ⟶ t') :
    baseChangeObj f i g t ⟶ baseChangeObj f i g t' :=
  ⟨(pullback (complementBaseChange i g)).map α.fst,
    (pullback (toY f g)).map α.snd, by exact baseChange_map_w f i g α⟩

/-- Base change of component maps preserves the identity of a glueing triple. -/
private theorem baseChange_map_id (t : category f i) :
    baseChangeMap f i g (𝟙 t) = 𝟙 (baseChangeObj f i g t) :=
  sorry

/-- Base change of component maps preserves composition of morphisms of glueing triples. -/
private theorem baseChange_map_comp {t t' t'' : category f i}
    (α : t ⟶ t') (β : t' ⟶ t'') :
    baseChangeMap f i g (α ≫ β) = baseChangeMap f i g α ≫ baseChangeMap f i g β :=
  sorry

/-- Pullback on both components and on their structural isomorphism defines base change
of quasi-coherent glueing triples. -/
def baseChange : category f i ⥤ category (f' f g) (i' i g) where
  obj t :=
    ⟨(pullback (complementBaseChange i g)).obj t.fst,
      (pullback (toY f g)).obj t.snd, pulledBackφ f i g t.iso⟩
  map {t t'} α :=
    ⟨(pullback (complementBaseChange i g)).map α.fst,
      (pullback (toY f g)).map α.snd, by exact baseChange_map_w f i g α⟩
  map_id := by exact baseChange_map_id f i g
  map_comp := by exact baseChange_map_comp f i g

end

namespace baseChange

/-- The first component of `baseChange` is quasi-coherent pullback along
`complementBaseChange`. -/
theorem obj_fst {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (t : category f i) :
    ((baseChange f i g).obj t).fst = (pullback (complementBaseChange i g)).obj t.fst :=
  rfl

/-- The second component of `baseChange` is quasi-coherent pullback along `toY`. -/
theorem obj_snd {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (t : category f i) :
    ((baseChange f i g).obj t).snd = (pullback (toY f g)).obj t.snd :=
  rfl

/-- The structural isomorphism of `baseChange` is `pulledBackφ` of the original
glueing isomorphism. -/
theorem obj_iso {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (t : category f i) :
    ((baseChange f i g).obj t).iso = pulledBackφ f i g t.iso :=
  rfl

end baseChange

section

variable {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
variable (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]

/-- The first components of base change of glueing and glueing after pullback are
compared by the canonical pullback-composition map. -/
private def functorBaseChangeNatTrans_fst (F : QCoh X) :
    ((baseChange f i g).obj ((functor f i).obj F)).fst ⟶
      ((functor (f' f g) (i' i g)).obj ((pullback g).obj F)).fst :=
  eqToHom ((baseChange.obj_fst f i g ((functor f i).obj F)).trans
      (congrArg ((pullback (complementBaseChange i g)).obj) (obj_fst f i F))) ≫
    (QCoh.pullbackCompIso (closedImmersionComplementι i) (complementBaseChange i g) ≪≫
      eqToIso (congrArg pullback (complementBaseChange_comp i g)) ≪≫
      (QCoh.pullbackCompIso g (closedImmersionComplementι (i' i g))).symm).hom.app F ≫
    eqToHom (obj_fst (f' f g) (i' i g) ((pullback g).obj F)).symm

/-- The second components of base change of glueing and glueing after pullback are
compared by the canonical pullback-composition map. -/
private def functorBaseChangeNatTrans_snd (F : QCoh X) :
    ((baseChange f i g).obj ((functor f i).obj F)).snd ⟶
      ((functor (f' f g) (i' i g)).obj ((pullback g).obj F)).snd :=
  eqToHom ((baseChange.obj_snd f i g ((functor f i).obj F)).trans
      (congrArg ((pullback (toY f g)).obj) (obj_snd f i F))) ≫
    (QCoh.pullbackCompIso f (toY f g) ≪≫
      eqToIso (congrArg pullback (pullback.condition (f := f) (g := g))) ≪≫
      (QCoh.pullbackCompIso g (f' f g)).symm).hom.app F ≫
    eqToHom (obj_snd (f' f g) (i' i g) ((pullback g).obj F)).symm

/-- The pullback-composition comparison maps respect the structural isomorphisms
of the two glueing triples associated to a quasi-coherent module. -/
private theorem functorBaseChangeNatTrans_app_w (F : QCoh X) :
    (pullback (restrictToComplement (f' f g) (i' i g))).map
        (functorBaseChangeNatTrans_fst f i g F) ≫
        (((functor (f' f g) (i' i g)).obj ((pullback g).obj F)).iso).hom =
      (((baseChange f i g).obj ((functor f i).obj F)).iso).hom ≫
        (pullback (closedImmersionComplementι (inverseImageι (f' f g) (i' i g)))).map
          (functorBaseChangeNatTrans_snd f i g F) :=
  sorry

/-- The canonical base-change comparison has the two pullback-composition maps as components. -/
@[no_expose] def functorBaseChangeNatTrans_app (F : QCoh X) :
    (baseChange f i g).obj ((functor f i).obj F) ⟶
      (functor (f' f g) (i' i g)).obj ((pullback g).obj F) where
  fst := functorBaseChangeNatTrans_fst f i g F
  snd := functorBaseChangeNatTrans_snd f i g F
  w := by exact functorBaseChangeNatTrans_app_w f i g F

/-- The comparison between base change of glueing and glueing after pullback is natural
in the quasi-coherent module. -/
private theorem functorBaseChangeNatTrans_naturality {F F' : QCoh X} (α : F ⟶ F') :
    (functor f i ⋙ baseChange f i g).map α ≫ functorBaseChangeNatTrans_app f i g F' =
      functorBaseChangeNatTrans_app f i g F ≫
        (pullback g ⋙ functor (f' f g) (i' i g)).map α :=
  sorry

/-- The canonical natural comparison between base change of glueing and glueing after pullback. -/
def functorBaseChangeNatTrans :
    functor f i ⋙ baseChange f i g ⟶ pullback g ⋙ functor (f' f g) (i' i g) where
  app := functorBaseChangeNatTrans_app f i g
  naturality _ _ α := by exact functorBaseChangeNatTrans_naturality f i g α

end

/-- The component of the canonical natural comparison is its explicit two-component map. -/
theorem functorBaseChangeNatTrans_app_eq {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] (F : QCoh X) :
    (functorBaseChangeNatTrans f i g).app F = functorBaseChangeNatTrans_app f i g F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

namespace AlgebraicGeometry.AlgebraicSpace

open QCoh.FormalGlueing

/-- Flat base change commutes with the canonical quasi-coherent formal-glueing functor. -/
instance functorBaseChange_isIso {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] [Flat g] :
    IsIso (functorBaseChangeNatTrans f i g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
