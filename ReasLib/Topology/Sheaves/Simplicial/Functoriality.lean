/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Simplicial.FiberRightAdjoint
public import ReasLib.Topology.Category.TopCat.DiagramOpens.SimplicialMap
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Functors

/-!
# Degreewise direct and inverse image of simplicial sheaves

Restriction to a degree commutes with direct image and canonically with inverse image
along the corresponding component map of a morphism of simplicial spaces.
-/

@[expose] public section
open CategoryTheory Functor TopologicalSpace TopCat Opposite
noncomputable section
universe u
namespace CategoryTheory.SimplicialObject
variable {X Y : SimplicialObject TopCat.{u}}

/-- Degree inclusion and inverse image of opens form a natural identity-component square. -/
theorem zariskiMap_fiber_naturality (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)
    {U V : Opens (X.obj n)} (morphism : U ⟶ V) :
    (DiagramOpens.fiber X n ⋙ zariskiMap f).map morphism ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (Opens.map (f.app n) ⋙ DiagramOpens.fiber Y n).map morphism := sorry

/-- The identity-component square for inverse image of opens and degree inclusion. -/
def zariskiMap_fiber (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ) :
    DiagramOpens.fiber X n ⋙ zariskiMap f ≅
      Opens.map (f.app n) ⋙ DiagramOpens.fiber Y n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun morphism => zariskiMap_fiber_naturality f n morphism)

/-- Components of `zariskiMap_fiber` are identity morphisms. -/
theorem zariskiMap_fiber_hom_app (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)
    (U : Opens (X.obj n)) :
    (zariskiMap_fiber f n).hom.app U = 𝟙 _ :=
  sorry

variable (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)

/-- Naturality identifies the two actual inverse-image opens in the square. -/
theorem fiberRightSquare_open (U : DiagramOpens X) (a : n ⟶ U.base) :
    fiberOpen Y n ((zariskiMap f).obj U) a =
      (Opens.map (f.app n)).obj (fiberOpen X n U a) := by
  change (Opens.map (Y.map a)).obj ((Opens.map (f.app U.base)).obj U.opens) =
    (Opens.map (f.app n)).obj ((Opens.map (X.map a)).obj U.opens)
  rw [← Opens.map_comp_obj, ← Opens.map_comp_obj, f.naturality]

/-- Transport of each product section along the componentwise inverse-image equality. -/
def fiberRightSquareHomApp (G : Sheaf (Opens.grothendieckTopology (Y.obj n)) (Type u))
    (U : (zariskiSite X)ᵒᵖ) :
    ((fiberRight Y n ⋙ (zariskiMap f).sheafPushforwardContinuous (Type u)
      (zariskiTopology X) (zariskiTopology Y)).obj G).obj.obj U ⟶
    ((TopCat.Sheaf.pushforward (Type u) (f.app n) ⋙ fiberRight X n).obj G).obj.obj U :=
  TypeCat.ofHom fun sections arrow =>
    G.obj.map (eqToHom (fiberRightSquare_open f n U.unop arrow).symm).op (sections arrow)

/-- Reverse transport of each product section along the inverse-image equality. -/
def fiberRightSquareInvApp (G : Sheaf (Opens.grothendieckTopology (Y.obj n)) (Type u))
    (U : (zariskiSite X)ᵒᵖ) :
    ((TopCat.Sheaf.pushforward (Type u) (f.app n) ⋙ fiberRight X n).obj G).obj.obj U ⟶
    ((fiberRight Y n ⋙ (zariskiMap f).sheafPushforwardContinuous (Type u)
      (zariskiTopology X) (zariskiTopology Y)).obj G).obj.obj U :=
  TypeCat.ofHom fun sections arrow =>
    G.obj.map (eqToHom (fiberRightSquare_open f n U.unop arrow)).op (sections arrow)

/-- Forward transport of product sections commutes with restriction. -/
theorem fiberRightSquare_hom_app_naturality
    (G : Sheaf (Opens.grothendieckTopology (Y.obj n)) (Type u))
    {U V : (zariskiSite X)ᵒᵖ} (morphism : U ⟶ V) :
    ((fiberRight Y n ⋙ (zariskiMap f).sheafPushforwardContinuous (Type u)
      (zariskiTopology X) (zariskiTopology Y)).obj G).obj.map morphism ≫
        fiberRightSquareHomApp f n G V =
    fiberRightSquareHomApp f n G U ≫
      ((TopCat.Sheaf.pushforward (Type u) (f.app n) ⋙ fiberRight X n).obj G).obj.map morphism := sorry

/-- Reverse transport of product sections commutes with restriction. -/
theorem fiberRightSquare_inv_app_naturality
    (G : Sheaf (Opens.grothendieckTopology (Y.obj n)) (Type u))
    {U V : (zariskiSite X)ᵒᵖ} (morphism : U ⟶ V) :
    ((TopCat.Sheaf.pushforward (Type u) (f.app n) ⋙ fiberRight X n).obj G).obj.map morphism ≫
        fiberRightSquareInvApp f n G V =
    fiberRightSquareInvApp f n G U ≫
      ((fiberRight Y n ⋙ (zariskiMap f).sheafPushforwardContinuous (Type u)
        (zariskiTopology X) (zariskiTopology Y)).obj G).obj.map morphism := sorry

/-- Right extensions commute with pushforward by transporting each indexed section
along the equality of inverse-image opens proved from naturality of `f`. -/
def fiberRightSquareComponent
    (G : Sheaf (Opens.grothendieckTopology (Y.obj n)) (Type u)) :
    (fiberRight Y n ⋙ (zariskiMap f).sheafPushforwardContinuous (Type u)
      (zariskiTopology X) (zariskiTopology Y)).obj G ≅
    (TopCat.Sheaf.pushforward (Type u) (f.app n) ⋙ fiberRight X n).obj G :=
    { hom := ⟨{ app := fiberRightSquareHomApp f n G
                naturality := fun _ _ morphism => fiberRightSquare_hom_app_naturality f n G morphism }⟩
      inv := ⟨{ app := fiberRightSquareInvApp f n G
                naturality := fun _ _ morphism => fiberRightSquare_inv_app_naturality f n G morphism }⟩
      hom_inv_id := by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        ext s
        funext a
        change G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a)).op
          (G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a).symm).op (s a)) = s a
        rw [← types_comp_apply, ← G.obj.map_comp]
        simp
      inv_hom_id := by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        ext s
        funext a
        change G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a).symm).op
          (G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a)).op (s a)) = s a
        rw [← types_comp_apply, ← G.obj.map_comp]
        simp }

/-- The right-extension comparison is natural in the component sheaf. -/
theorem fiberRightSquare_naturality
    {G H : Sheaf (Opens.grothendieckTopology (Y.obj n)) (Type u)} (morphism : G ⟶ H) :
    (fiberRight Y n ⋙ (zariskiMap f).sheafPushforwardContinuous (Type u)
      (zariskiTopology X) (zariskiTopology Y)).map morphism ≫
        (fiberRightSquareComponent f n H).hom =
    (fiberRightSquareComponent f n G).hom ≫
      (TopCat.Sheaf.pushforward (Type u) (f.app n) ⋙ fiberRight X n).map morphism := sorry

/-- Product right extension commutes with componentwise direct image. -/
def fiberRightSquare :
    fiberRight Y n ⋙ (zariskiMap f).sheafPushforwardContinuous (Type u)
      (zariskiTopology X) (zariskiTopology Y) ≅
    TopCat.Sheaf.pushforward (Type u) (f.app n) ⋙ fiberRight X n :=
  NatIso.ofComponents (fiberRightSquareComponent f n)
    (fun morphism => fiberRightSquare_naturality f n morphism)


/-- Continuity of the target composite of `zariskiMap_fiber`, transported from
`DiagramOpens.fiber X n ⋙ zariskiMap f`. -/
instance zariskiMap_fiber_isContinuous :
    (Opens.map (f.app n) ⋙ DiagramOpens.fiber Y n).IsContinuous
      (Opens.grothendieckTopology (X.obj n)) (zariskiTopology Y) :=
  isContinuous_comp' (zariskiMap_fiber f n)
    (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X) (zariskiTopology Y)

/-- Pushforward along `zariskiMap f` then restrict to `X.obj n` is isomorphic to restrict
to `Y.obj n` then pushforward along `f.app n`. -/
def zariskiMap_pushforwardRestrict :
    (zariskiMap f).sheafPushforwardContinuous (Type u)
          (zariskiTopology X) (zariskiTopology Y) ⋙
        (DiagramOpens.fiber X n).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X) ≅
      (DiagramOpens.fiber Y n).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology (Y.obj n)) (zariskiTopology Y) ⋙
        TopCat.Sheaf.pushforward (Type u) (f.app n) :=
  sheafPushforwardContinuousComp' (zariskiMap_fiber f n) (Type u)
      (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X) (zariskiTopology Y) ≪≫
    (sheafPushforwardContinuousComp (Opens.map (f.app n)) (DiagramOpens.fiber Y n) (Type u)
      (Opens.grothendieckTopology (X.obj n))
      (Opens.grothendieckTopology (Y.obj n)) (zariskiTopology Y)).symm

/-- Degree restriction of direct image is componentwise direct image. -/
def zariskiPushforward_component (G : Sheaf (zariskiTopology Y) (Type u)) :
    (sheafFiber X n (Type u)).obj
      (((zariskiMap f).sheafPushforwardContinuous (Type u)
        (zariskiTopology X) (zariskiTopology Y)).obj G) ≅
      (TopCat.Sheaf.pushforward (Type u) (f.app n)).obj ((sheafFiber Y n (Type u)).obj G) :=
  (zariskiMap_pushforwardRestrict f n).app G

/-- Sections of `(f_Zar,* G)_n` over an open of `X.obj n` agree with sections of `f_n,* G_n`. -/
theorem zariskiPushforward_component_obj (G : Sheaf (zariskiTopology Y) (Type u))
    (U : Opens (X.obj n)) :
    (((sheafFiber X n (Type u)).obj
        (((zariskiMap f).sheafPushforwardContinuous (Type u)
          (zariskiTopology X) (zariskiTopology Y)).obj G)).obj.obj (op U)) =
      (((TopCat.Sheaf.pushforward (Type u) (f.app n)).obj
        ((sheafFiber Y n (Type u)).obj G)).obj.obj (op U)) :=
  sorry

variable [HasWeakSheafify (zariskiTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology (Y.obj n)) (Type u)]
variable [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
variable [∀ P : (Opens (X.obj n))ᵒᵖ ⥤ Type u, (Opens.map (f.app n)).op.HasLeftKanExtension P]

/-- The mixed Beck–Chevalley mate
`(restrict_X ⋙ f_n⁻¹) ⟶ (f_Zar⁻¹ ⋙ restrict_Y)` of `zariskiMap_pushforwardRestrict`.
Its inverse-image comparison is specified by the canonical mixed mate. -/
def zariskiMap_pullbackRestrict_mate :
    (DiagramOpens.fiber X n).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X) ⋙
        TopCat.Sheaf.pullback (Type u) (f.app n) ⟶
      (zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y) ⋙
        (DiagramOpens.fiber Y n).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology (Y.obj n)) (zariskiTopology Y) :=
  (mateEquiv
      ((zariskiMap f).sheafAdjunctionContinuous (Type u)
        (zariskiTopology X) (zariskiTopology Y))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f.app n))).symm
    (TwoSquare.mk _ _ _ _ (zariskiMap_pushforwardRestrict f n).hom)

/-- The mixed Beck–Chevalley isomorphism
`(f_Zar⁻¹ ⋙ restrict_Y) ≅ (restrict_X ⋙ f_n⁻¹)` obtained from uniqueness of
left adjoints to the explicit product right-extension square. -/
def zariskiMap_pullbackRestrict :
    (zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y) ⋙
      sheafFiber Y n (Type u) ≅
    sheafFiber X n (Type u) ⋙ TopCat.Sheaf.pullback (Type u) (f.app n) :=
  Adjunction.leftAdjointUniq
    ((((zariskiMap f).sheafAdjunctionContinuous (Type u)
      (zariskiTopology X) (zariskiTopology Y)).comp
      (sheafFiberRightAdjunction Y n)).ofNatIsoRight (fiberRightSquare f n))
    ((sheafFiberRightAdjunction X n).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f.app n)))


/-- Degree restriction of inverse image is canonically componentwise inverse image. -/
def zariskiPullback_component (F : Sheaf (zariskiTopology X) (Type u)) :
    (sheafFiber Y n (Type u)).obj
      (((zariskiMap f).sheafPullback (Type u)
        (zariskiTopology X) (zariskiTopology Y)).obj F) ≅
      (TopCat.Sheaf.pullback (Type u) (f.app n)).obj ((sheafFiber X n (Type u)).obj F) :=
  (zariskiMap_pullbackRestrict f n).app F

/-- The inverse of `zariskiMap_pullbackRestrict` agrees with the mixed mate of
`zariskiMap_pushforwardRestrict`. -/
theorem zariskiMap_pullbackRestrict_inv_eq_mate :
    (zariskiMap_pullbackRestrict f n).inv = zariskiMap_pullbackRestrict_mate f n :=
  sorry

end CategoryTheory.SimplicialObject
