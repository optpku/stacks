module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Square
public import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Tactic.CrossRefAttribute

/-!
# The fibre-product right adjoint for module categories

Given a commuting square of commutative rings, extension of scalars defines a functor into the
categorical pullback of two module categories.  This file constructs its right adjoint explicitly:
on an object `(N, M', φ)` it is the kernel of the difference between the two canonical maps out of
`N × M'`.

@stack 0D2F
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.Pullback

variable {R R' B B' : Type u}
variable [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
variable {s : B →+* R} {t : R' →+* R}

/-- The pullback category of modules used by the change-of-rings square. -/
@[stacks 0D2F "module-category pullback"]
abbrev Category (s : B →+* R) (t : R' →+* R) :=
  CategoricalPullback (ModuleCat.extendScalars.{u, u, u} s)
    (ModuleCat.extendScalars.{u, u, u} t)

/-- The product module containing the fibre-product right adjoint as a kernel. -/
@[stacks 0D2F "ambient product for the pullback right adjoint"]
abbrev sourceObj (f : B' →+* B) (g : B' →+* R') (X : Category s t) : ModuleCat.{u} B' :=
  Limits.prod ((ModuleCat.restrictScalars f).obj X.fst)
    ((ModuleCat.restrictScalars g).obj X.snd)

/-- The common target of the two comparison maps defining the fibre-product module. -/
@[stacks 0D2F "common target of the pullback comparison maps"]
abbrev targetObj (g : B' →+* R') (X : Category s t) : ModuleCat.{u} B' :=
  (ModuleCat.restrictScalars (t.comp g)).obj ((ModuleCat.extendScalars t).obj X.snd)

/-- Restriction of scalars along equal composite ring maps, represented by the identity transport. -/
@[stacks 0D2F "restriction transport across a commuting ring square"]
def restrictScalarsCommHom (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (s.comp f)).obj M ⟶
      (ModuleCat.restrictScalars (t.comp g)).obj M :=
  (eqToIso (congrArg (fun h ↦ (ModuleCat.restrictScalars h).obj M) hcomm)).hom

/-- The comparison from the restricted first component to the common base-changed target. -/
@[stacks 0D2F "left comparison map for the pullback module"]
abbrev leftMap (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (X : Category s t) :
    (ModuleCat.restrictScalars f).obj X.fst ⟶ targetObj g X :=
  (ModuleCat.restrictScalars f).map ((ModuleCat.extendRestrictScalarsAdj s).unit.app X.fst) ≫
    (ModuleCat.restrictScalarsComp f s).inv.app ((ModuleCat.extendScalars s).obj X.fst) ≫
    (ModuleCat.restrictScalars (s.comp f)).map X.iso.hom ≫
    restrictScalarsCommHom f g hcomm ((ModuleCat.extendScalars t).obj X.snd)

/-- The comparison from the restricted second component to the common base-changed target. -/
@[stacks 0D2F "right comparison map for the pullback module"]
abbrev rightMap (g : B' →+* R') (X : Category s t) :
    (ModuleCat.restrictScalars g).obj X.snd ⟶ targetObj g X :=
  (ModuleCat.restrictScalars g).map ((ModuleCat.extendRestrictScalarsAdj t).unit.app X.snd) ≫
    (ModuleCat.restrictScalarsComp g t).inv.app ((ModuleCat.extendScalars t).obj X.snd)

/-- The left comparison map from the ambient product module. -/
@[stacks 0D2F "left map from the ambient product module"]
abbrev productLeftMap (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) (X : Category s t) : sourceObj f g X ⟶ targetObj g X :=
  Limits.prod.fst ≫ leftMap f g hcomm X

/-- The right comparison map from the ambient product module. -/
@[stacks 0D2F "right map from the ambient product module"]
abbrev productRightMap (f : B' →+* B) (g : B' →+* R')
    (X : Category s t) : sourceObj f g X ⟶ targetObj g X :=
  Limits.prod.snd ≫ rightMap g X

/-- The difference map whose kernel is the fibre-product module. -/
@[stacks 0D2F "difference map defining the pullback module"]
abbrev difference (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (X : Category s t) : sourceObj f g X ⟶ targetObj g X :=
  productLeftMap f g hcomm X - productRightMap f g X

/-- The ambient product maps preserve identity morphisms. -/
theorem sourceFunctor_map_id (f : B' →+* B) (g : B' →+* R') (X : Category s t) :
    Limits.prod.map ((ModuleCat.restrictScalars f).map (𝟙 X.fst))
        ((ModuleCat.restrictScalars g).map (𝟙 X.snd)) = 𝟙 (sourceObj f g X) := sorry

/-- The ambient product maps preserve composition. -/
theorem sourceFunctor_map_comp (f : B' →+* B) (g : B' →+* R')
    {X Y Z : Category s t} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    Limits.prod.map ((ModuleCat.restrictScalars f).map (φ.fst ≫ ψ.fst))
        ((ModuleCat.restrictScalars g).map (φ.snd ≫ ψ.snd)) =
      Limits.prod.map ((ModuleCat.restrictScalars f).map φ.fst)
          ((ModuleCat.restrictScalars g).map φ.snd) ≫
        Limits.prod.map ((ModuleCat.restrictScalars f).map ψ.fst)
          ((ModuleCat.restrictScalars g).map ψ.snd) := sorry

/-- The ambient product modules form a functor on the pullback category. -/
@[stacks 0D2F "ambient product functor"]
def sourceFunctor (f : B' →+* B) (g : B' →+* R') : Category s t ⥤ ModuleCat.{u} B' where
  obj X := sourceObj f g X
  map φ := Limits.prod.map ((ModuleCat.restrictScalars f).map φ.fst)
    ((ModuleCat.restrictScalars g).map φ.snd)
  map_id X := sourceFunctor_map_id f g X
  map_comp φ ψ := sourceFunctor_map_comp f g φ ψ

/-- The common targets of the two comparison maps preserve identity morphisms. -/
theorem targetFunctor_map_id (g : B' →+* R') (X : Category s t) :
    (ModuleCat.restrictScalars (t.comp g)).map
        ((ModuleCat.extendScalars t).map (𝟙 X.snd)) = 𝟙 (targetObj g X) := sorry

/-- The common targets of the two comparison maps preserve composition. -/
theorem targetFunctor_map_comp (g : B' →+* R') {X Y Z : Category s t}
    (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (ModuleCat.restrictScalars (t.comp g)).map
        ((ModuleCat.extendScalars t).map (φ.snd ≫ ψ.snd)) =
      (ModuleCat.restrictScalars (t.comp g)).map ((ModuleCat.extendScalars t).map φ.snd) ≫
        (ModuleCat.restrictScalars (t.comp g)).map
          ((ModuleCat.extendScalars t).map ψ.snd) := sorry

/-- The common target modules form a functor on the pullback category. -/
@[stacks 0D2F "common target functor"]
def targetFunctor (g : B' →+* R') : Category s t ⥤ ModuleCat.{u} B' where
  obj X := targetObj g X
  map φ := (ModuleCat.restrictScalars (t.comp g)).map
    ((ModuleCat.extendScalars t).map φ.snd)
  map_id X := targetFunctor_map_id g X
  map_comp φ ψ := targetFunctor_map_comp g φ ψ

/-- The difference maps are natural in the pullback-module variable. -/
theorem difference_naturality (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) {X Y : Category s t} (φ : X ⟶ Y) :
    (sourceFunctor (s := s) (t := t) f g).map φ ≫ difference f g hcomm Y =
      difference f g hcomm X ≫ (targetFunctor (t := t) g).map φ := sorry

/-- The natural transformation whose pointwise kernel is the fibre-product module functor. -/
@[stacks 0D2F "fibre-product difference transformation"]
def differenceNatTrans (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) :
    sourceFunctor (s := s) (t := t) f g ⟶ targetFunctor (t := t) g where
  app X := difference f g hcomm X
  naturality := fun {X Y} φ ↦ difference_naturality f g hcomm (X := X) (Y := Y) φ

/-- The arrow-valued functor packaging the fibre-product difference maps. -/
@[stacks 0D2F "arrow presentation of the fibre-product module"]
def arrow (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    Category s t ⥤ Arrow (ModuleCat.{u} B') where
  obj X := Arrow.mk ((differenceNatTrans f g hcomm).app X)
  map φ := Arrow.homMk' ((sourceFunctor (s := s) (t := t) f g).map φ)
    ((targetFunctor (t := t) g).map φ)
    ((differenceNatTrans f g hcomm).naturality φ)

/-- The explicit fibre-product module functor, defined as the pointwise kernel of `difference`. -/
@[stacks 0D2F "fibre-product right adjoint"]
abbrev rightAdjoint (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    Category s t ⥤ ModuleCat.{u} B' :=
  arrow f g hcomm ⋙ Limits.ker (ModuleCat.{u} B')

/-- A compatible pair of maps equalizes the defining difference morphism. -/
theorem lift_condition (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) {L : ModuleCat.{u} B'} {X : Category s t}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (leftMap f g hcomm X) (rightMap g X)) :
    Limits.prod.lift u v ≫ difference f g hcomm X = 0 := sorry

/-- The universal map from a compatible pair into the fibre-product module. -/
@[stacks 0D2F "universal lift into the pullback module"]
abbrev lift (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    {L : ModuleCat.{u} B'} {X : Category s t}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (leftMap f g hcomm X) (rightMap g X)) :
    L ⟶ kernel (difference f g hcomm X) :=
  kernel.lift (difference f g hcomm X) (Limits.prod.lift u v)
    (lift_condition f g hcomm u v hcompat)

/-- Transposing a pullback morphism gives a compatible pair for the kernel construction. -/
theorem hom_compatible (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) (L : ModuleCat.{u} B') (X : Category s t)
    (a : (ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).obj L ⟶ X) :
    CommSq (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _) a.fst)
      (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _) a.snd)
      (leftMap f g hcomm X) (rightMap g X) := sorry

/-- A morphism into the kernel yields a compatible pair of component maps. -/
theorem kernelHom_compatible (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) {L : ModuleCat.{u} B'} {X : Category s t}
    (k : L ⟶ kernel (difference f g hcomm X)) :
    CommSq (k ≫ kernel.ι (difference f g hcomm X) ≫ Limits.prod.fst)
      (k ≫ kernel.ι (difference f g hcomm X) ≫ Limits.prod.snd)
      (leftMap f g hcomm X) (rightMap g X) := sorry

/-- The adjoint transposes of a compatible pair satisfy the categorical-pullback square. -/
theorem compatiblePairToPullback_condition (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) {L : ModuleCat.{u} B'} {X : Category s t}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (leftMap f g hcomm X) (rightMap g X)) :
    (ModuleCat.extendScalars s).map
          (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm u) ≫ X.iso.hom =
      ((ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).obj L).iso.hom ≫
        (ModuleCat.extendScalars t).map
          (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).symm v) := sorry

/-- A compatible pair transposes to a morphism into the categorical pullback. -/
@[stacks 0D2F "compatible pair as a pullback morphism"]
abbrev compatiblePairToPullback (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) {L : ModuleCat.{u} B'} {X : Category s t}
    (u : L ⟶ (ModuleCat.restrictScalars f).obj X.fst)
    (v : L ⟶ (ModuleCat.restrictScalars g).obj X.snd)
    (hcompat : CommSq u v (leftMap f g hcomm X) (rightMap g X)) :
    (ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).obj L ⟶ X :=
  CategoricalPullback.Hom.mk
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm u)
    (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).symm v)
    (compatiblePairToPullback_condition f g hcomm u v hcompat)

/-- The forward map of the adjunction Hom equivalence. -/
@[stacks 0D2F "forward map of the pullback adjunction equivalence"]
abbrev homEquivToFun (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) (L : ModuleCat.{u} B') (X : Category s t) :
    ((ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).obj L ⟶ X) →
      (L ⟶ (rightAdjoint f g hcomm).obj X) :=
  fun a ↦ lift f g hcomm
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _) a.fst)
    (((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _) a.snd)
    (hom_compatible f g hcomm L X a)

/-- The inverse map of the adjunction Hom equivalence. -/
@[stacks 0D2F "inverse map of the pullback adjunction equivalence"]
abbrev homEquivInvFun (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) (L : ModuleCat.{u} B') (X : Category s t) :
    (L ⟶ (rightAdjoint f g hcomm).obj X) →
      ((ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).obj L ⟶ X) :=
  fun k ↦ compatiblePairToPullback f g hcomm
    (k ≫ kernel.ι (difference f g hcomm X) ≫ Limits.prod.fst)
    (k ≫ kernel.ι (difference f g hcomm X) ≫ Limits.prod.snd)
    (kernelHom_compatible f g hcomm k)

/-- The two explicit directions of the Hom equivalence are left inverses. -/
theorem homEquiv_left_inv (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) (L : ModuleCat.{u} B') (X : Category s t)
    (a : (ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).obj L ⟶ X) :
    homEquivInvFun f g hcomm L X (homEquivToFun f g hcomm L X a) = a := sorry

/-- The two explicit directions of the Hom equivalence are right inverses. -/
theorem homEquiv_right_inv (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) (L : ModuleCat.{u} B') (X : Category s t)
    (k : L ⟶ (rightAdjoint f g hcomm).obj X) :
    homEquivToFun f g hcomm L X (homEquivInvFun f g hcomm L X k) = k := sorry

/-- The Hom equivalence for extension of scalars into the pullback and the kernel functor. -/
@[stacks 0D2F "Hom equivalence for the fibre-product right adjoint"]
def homEquiv (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g)
    (L : ModuleCat.{u} B') (X : Category s t) :
    ((ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).obj L ⟶ X) ≃
      (L ⟶ (rightAdjoint f g hcomm).obj X) where
  toFun := homEquivToFun f g hcomm L X
  invFun := homEquivInvFun f g hcomm L X
  left_inv := homEquiv_left_inv f g hcomm L X
  right_inv := homEquiv_right_inv f g hcomm L X

/-- The inverse Hom equivalence is natural in the module variable. -/
theorem homEquiv_naturality_left_symm (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) {L₁ L₂ : ModuleCat.{u} B'} {X : Category s t}
    (α : L₁ ⟶ L₂) (k : L₂ ⟶ (rightAdjoint f g hcomm).obj X) :
    (homEquiv f g hcomm L₁ X).symm (α ≫ k) =
      (ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).map α ≫
        (homEquiv f g hcomm L₂ X).symm k := sorry

/-- The Hom equivalence is natural in the pullback-object variable. -/
theorem homEquiv_naturality_right (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) {L : ModuleCat.{u} B'} {X Y : Category s t}
    (ψ : (ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).obj L ⟶ X)
    (β : X ⟶ Y) :
    homEquiv f g hcomm L Y (ψ ≫ β) =
      homEquiv f g hcomm L X ψ ≫ (rightAdjoint f g hcomm).map β := sorry

/-- Lemma 15.5.4: extension of scalars into the module-category pullback is left adjoint to the
explicit fibre-product module functor. -/
@[stacks 0D2F "Lemma 15.5.4 module pullback adjunction"]
def adjunction (f : B' →+* B) (g : B' →+* R') (hcomm : s.comp f = t.comp g) :
    ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm ⊣ rightAdjoint f g hcomm :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv f g hcomm
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm f g hcomm
      homEquiv_naturality_right := homEquiv_naturality_right f g hcomm }

/-- The canonical pullback base-change functor has a right adjoint. -/
@[stacks 0D2F "pullback base-change functor is a left adjoint", instance]
noncomputable instance toPullbackIsLeftAdjoint (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) :
    (ModuleCat.extendScalarsToPullback.{u, u} s t f g hcomm).IsLeftAdjoint := sorry

/-- The fibre-product module functor is a right adjoint. -/
@[stacks 0D2F "fibre-product module functor is a right adjoint", instance]
noncomputable instance rightAdjointIsRightAdjoint (f : B' →+* B) (g : B' →+* R')
    (hcomm : s.comp f = t.comp g) : (rightAdjoint f g hcomm).IsRightAdjoint := sorry

end CategoryTheory.ModuleCat.Pullback
