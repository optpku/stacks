/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictScalars.Pair

/-!
# Morphisms to restriction of scalars

Morphisms from the sheaf of an algebraic space to restriction of scalars
correspond canonically to a base morphism and a lift from its fibre product.
-/

@[expose] public section

-- Export the bodies of private implementation definitions so the public
-- constructions retain their definitional computation rules.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-- Scheme-valued and algebraic-space-valued pairs use the same canonical carrier. -/
def pairOverEquiv {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
    (T : Over S) : RestrictScalars.Pair f g (ofOver T) ≃ Pair f g T :=
  Equiv.refl _

/-- Transport of a pair preserves its base morphism. -/
theorem pairOverEquiv_base {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) {T : Over S} (p : RestrictScalars.Pair f g (ofOver T)) :
    (pairOverEquiv f g T p).a = p.a := rfl

/-- Transport of a pair precomposes its lift with the canonical pullback comparison. -/
theorem pairOverEquiv_lift {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) {T : Over S} (p : RestrictScalars.Pair f g (ofOver T)) :
    (pairOverEquiv f g T p).b = (fiberPullbackIso g p.a).hom ≫ p.b :=
  (Category.id_comp _).symm

/-- Restriction of a geometric pair along scheme-valued points is natural. -/
private theorem ofPair_hom_naturality {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (p : RestrictScalars.Pair f g T)
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (toSheaf.obj T).obj.map φ ≫
        TypeCat.ofHom (fun x ↦ pairOverEquiv f g V.unop
          (RestrictScalars.Pair.map p (yonedaEquiv.symm x.down : ofOver V.unop ⟶ T))) =
      TypeCat.ofHom (fun x ↦ pairOverEquiv f g U.unop
          (RestrictScalars.Pair.map p (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T))) ≫
        (sheaf f g).obj.map φ := sorry

private def ofPair_hom {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (p : RestrictScalars.Pair f g T) :
    (toSheaf.obj T).obj ⟶ (sheaf f g).obj where
  app U := TypeCat.ofHom fun x ↦
    pairOverEquiv f g U.unop
      (RestrictScalars.Pair.map p (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T))
  naturality := fun _ _ φ ↦ ofPair_hom_naturality p φ

/-- A geometric pair defines a sheaf morphism to restriction of scalars. -/
def ofPair {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (p : RestrictScalars.Pair f g T) : toSheaf.obj T ⟶ sheaf f g :=
  Sheaf.homEquiv.symm (ofPair_hom p)

/-- The sheaf morphism associated to a pair restricts it along each scheme-valued point. -/
theorem ofPair_hom_app {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} (p : RestrictScalars.Pair f g T) (U : (Over S)ᵒᵖ)
    (x : ULift.{u + 1} (T.functorOfPoints.obj U)) :
    (ofPair p).hom.app U x =
      pairOverEquiv f g U.unop
        (RestrictScalars.Pair.map p (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T)) := rfl

private def toPair_a {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g) : T ⟶ B :=
  (fullyFaithfulULiftFunctor.{u + 1, u}.whiskeringRight (Over S)ᵒᵖ).preimage
    (v ≫ toBase f g).hom

private def toPairEval {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g)
    {U : (Over S)ᵒᵖ} (t : T.functorOfPoints.obj U) : Pair f g U.unop :=
  (v.hom.app U) (ULift.up t)

private def toPairFst {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g)
    {U : (Over S)ᵒᵖ} (x : (pullback (toPair_a v) g).functorOfPoints.obj U) :
    T.functorOfPoints.obj U :=
  (pullback.fst (toPair_a v) g).app U x

private def toPairSnd {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g)
    {U : (Over S)ᵒᵖ} (x : (pullback (toPair_a v) g).functorOfPoints.obj U) :
    Z.functorOfPoints.obj U :=
  (pullback.snd (toPair_a v) g).app U x

/-- The evaluated base point and the second pullback projection agree over `B`. -/
private theorem toPairSection_overB {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g)
    {U : (Over S)ᵒᵖ} (x : (pullback (toPair_a v) g).functorOfPoints.obj U) :
    𝟙 (ofOver U.unop) ≫ (toPairEval v (toPairFst v x)).a =
      (yonedaEquiv.symm (toPairSnd v x) : ofOver U.unop ⟶ Z) ≫ g := sorry

private def toPairSection {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g)
    {U : (Over S)ᵒᵖ} (x : (pullback (toPair_a v) g).functorOfPoints.obj U) :
    ofOver U.unop ⟶ fiber g (toPairEval v (toPairFst v x)).a :=
  Limits.pullback.lift (𝟙 _)
    (yonedaEquiv.symm (toPairSnd v x) : ofOver U.unop ⟶ Z)
    (toPairSection_overB v x)

/-- Evaluating the lift on the canonical section commutes with change of test scheme. -/
private theorem toPair_b_naturality {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g)
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (pullback (toPair_a v) g).functorOfPoints.map φ ≫
        TypeCat.ofHom (fun x ↦
          yonedaEquiv (toPairSection v x ≫ (toPairEval v (toPairFst v x)).b)) =
      TypeCat.ofHom (fun x ↦
          yonedaEquiv (toPairSection v x ≫ (toPairEval v (toPairFst v x)).b)) ≫
        X.functorOfPoints.map φ := sorry

private def toPair_b {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g) :
    pullback (toPair_a v) g ⟶ X where
  app U := TypeCat.ofHom fun x ↦
    yonedaEquiv (toPairSection v x ≫ (toPairEval v (toPairFst v x)).b)
  naturality := fun _ _ φ ↦ toPair_b_naturality v φ

/-- The reconstructed lift commutes with the morphisms to `Z`. -/
private theorem toPair_overZ {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g) :
    toPair_b v ≫ f = pullback.snd (toPair_a v) g := sorry

/-- A sheaf morphism to restriction of scalars determines a geometric pair. -/
def toPair {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (v : toSheaf.obj T ⟶ sheaf f g) : RestrictScalars.Pair f g T where
  a := toPair_a v
  b := toPair_b v
  overZ := toPair_overZ v

/-- Reconstructing a pair from a sheaf morphism and taking its associated morphism
recovers the original morphism. -/
theorem ofPair_toPair {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (v : toSheaf.obj T ⟶ sheaf f g) :
    ofPair (toPair v) = v := sorry

/-- Reconstructing a pair from its associated sheaf morphism recovers the pair. -/
theorem toPair_ofPair {S : Scheme.{u}} {X Z B T : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (p : RestrictScalars.Pair f g T) :
    toPair (ofPair p) = p := sorry

/-- Sheaf morphisms to restriction of scalars correspond canonically to geometric pairs. -/
def homEquiv {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B) :
    (toSheaf.obj T ⟶ sheaf f g) ≃ RestrictScalars.Pair f g T where
  toFun := toPair
  invFun := ofPair
  left_inv := ofPair_toPair
  right_inv := toPair_ofPair

/-- The canonical correspondence sends a sheaf morphism to its reconstructed pair. -/
theorem homEquiv_apply {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (v : toSheaf.obj T ⟶ sheaf f g) :
    homEquiv f g v = toPair v := rfl

/-- The inverse correspondence sends a geometric pair to its associated sheaf morphism. -/
theorem homEquiv_symm_apply {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (p : RestrictScalars.Pair f g T) :
    (homEquiv f g).symm p = ofPair p := rfl

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
