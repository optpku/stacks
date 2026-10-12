/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InverseImage
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# Inverse image of relative derivations

Relative derivations with values in an inverse-image module are equivalent to
relative derivations with values in its pushforward.  Both directions are
given on sections, so the inverse transport does not select data from an
isomorphism proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u v w

namespace SheafOfModules.RelativeDerivation.InverseImage

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify K CommRingCat.{max u v}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable {M : SheafOfModules
  (ringSheaf K ((RingedSite.InverseImage.ringPullback
    (J := J) (K := K) F).obj O₂))}

/-- A module over a commutative ring, regarded as a module over its opposite
ring through the canonical identification. -/
@[no_expose] abbrev oppositeModule (R : Type*) [CommRing R]
    (N : Type*) [AddCommGroup N] [Module R N] : Module Rᵐᵒᵖ N :=
  Module.compHom N
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := fun x y ↦ by
        change MulOpposite.unop y * MulOpposite.unop x = _
        rw [mul_comm]
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The trivial square-zero extension of a commutative ring by a module. -/
@[no_expose] def squareZeroRing (R : CommRingCat.{w})
    (N : ModuleCat.{w} R) : CommRingCat.{w} :=
  -- Local instance justification (instance diamond): the square-zero extension uses the right action canonically induced by the commutative left action.
  letI : Module Rᵐᵒᵖ N := oppositeModule R N
  -- Local instance justification (proof-local temporary data): centrality is needed only to assemble the commutative square-zero ring structure.
  letI : IsCentralScalar R N := ⟨fun _ _ ↦ rfl⟩
  CommRingCat.of (TrivSqZeroExt R N)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction maps of a ring sheaf and a module sheaf induce restriction maps
on their trivial square-zero extensions. -/
@[no_expose] def squareZeroMap
    (R : Sheaf K CommRingCat.{max u v})
    (N : SheafOfModules (ringSheaf K R)) {U V : Dᵒᵖ} (rho : U ⟶ V) :
    squareZeroRing (R.obj.obj U) (N.val.obj U) ⟶
      squareZeroRing (R.obj.obj V) (N.val.obj V) :=
  -- Local instance justification (instance diamond): the square-zero extension uses the right action canonically induced by the commutative left action.
  letI : Module (R.obj.obj U)ᵐᵒᵖ (N.val.obj U) :=
    oppositeModule (R.obj.obj U) (N.val.obj U)
  -- Local instance justification (proof-local temporary data): centrality is needed only to assemble the source square-zero ring structure.
  letI : IsCentralScalar (R.obj.obj U) (N.val.obj U) := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (instance diamond): the square-zero extension uses the right action canonically induced by the commutative left action.
  letI : Module (R.obj.obj V)ᵐᵒᵖ (N.val.obj V) :=
    oppositeModule (R.obj.obj V) (N.val.obj V)
  -- Local instance justification (proof-local temporary data): centrality is needed only to assemble the target square-zero ring structure.
  letI : IsCentralScalar (R.obj.obj V) (N.val.obj V) := ⟨fun _ _ ↦ rfl⟩
  CommRingCat.ofHom
    { toFun := fun x ↦
        (R.obj.map rho x.1, N.val.map rho x.2)
      map_zero' := by
        ext
        · change R.obj.map rho 0 = 0
          exact map_zero _
        · change N.val.map rho 0 = 0
          exact map_zero _
      map_one' := by
        ext
        · change R.obj.map rho 1 = 1
          exact map_one _
        · change N.val.map rho 0 = 0
          exact map_zero _
      map_add' := by
        intro x y
        ext
        · change R.obj.map rho (x.1 + y.1) = _
          exact map_add _ _ _
        · change N.val.map rho (x.2 + y.2) = _
          exact map_add _ _ _
      map_mul' := by
        intro x y
        ext
        · change R.obj.map rho (x.1 * y.1) = _
          exact map_mul _ _ _
        · change N.val.map rho (x.1 • y.2 + y.1 • x.2) =
            (ringSheaf K R).obj.map rho x.1 • N.val.map rho y.2 +
              (ringSheaf K R).obj.map rho y.1 • N.val.map rho x.2
          rw [map_add, N.val.map_smul, N.val.map_smul] }

/-- The presheaf of trivial square-zero extensions of a commutative ring sheaf
by one of its module sheaves. -/
@[no_expose] def squareZeroPresheaf
    (R : Sheaf K CommRingCat.{max u v})
    (N : SheafOfModules (ringSheaf K R)) :
    Dᵒᵖ ⥤ CommRingCat.{max u v} where
  obj U := squareZeroRing (R.obj.obj U) (N.val.obj U)
  map rho := squareZeroMap R N rho
  map_id U := by
    ext x
    change (R.obj.map (𝟙 U) x.1, N.val.map (𝟙 U) x.2) = x
    ext <;> simp
  map_comp rho sigma := by
    ext x
    change (R.obj.map (rho ≫ sigma) x.1, N.val.map (rho ≫ sigma) x.2) =
      (R.obj.map sigma (R.obj.map rho x.1),
        N.val.map sigma (N.val.map rho x.2))
    ext <;> simp

/-- The presheaf of trivial square-zero extensions of a ring sheaf by a module
sheaf satisfies the sheaf condition. -/
private theorem squareZeroPresheaf_isSheaf
    (R : Sheaf K CommRingCat.{max u v})
    (N : SheafOfModules (ringSheaf K R)) :
    Presheaf.IsSheaf K (squareZeroPresheaf R N) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget K
    (P' := squareZeroPresheaf R N)
    (CategoryTheory.forget CommRingCat.{max u v})).mpr
  let R' : Sheaf K (Type (max u v)) :=
    ⟨R.obj ⋙ CategoryTheory.forget CommRingCat.{max u v},
      (Presheaf.isSheaf_iff_isSheaf_forget K R.obj
        (CategoryTheory.forget CommRingCat.{max u v})).mp R.property⟩
  let N' : Sheaf K (Type (max u v)) :=
    ⟨N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max u v},
      (Presheaf.isSheaf_iff_isSheaf_forget K N.val.presheaf
        (CategoryTheory.forget AddCommGrpCat.{max u v})).mp N.isSheaf⟩
  let e : squareZeroPresheaf R N ⋙
        CategoryTheory.forget CommRingCat.{max u v} ≅ (R'.obj ⊗ N'.obj) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
  exact (Presheaf.isSheaf_of_iso_iff e).mpr
    (Sheaf.tensorProd_isSheaf K R' N')

/-- The sheaf of trivial square-zero extensions of a commutative ring sheaf by
one of its module sheaves. -/
@[no_expose] def squareZeroSheaf
    (R : Sheaf K CommRingCat.{max u v})
    (N : SheafOfModules (ringSheaf K R)) :
    Sheaf K CommRingCat.{max u v} :=
  ⟨squareZeroPresheaf R N, squareZeroPresheaf_isSheaf R N⟩

/-- The module coordinate of a section of a trivial square-zero extension
sheaf. -/
@[no_expose] def squareZeroSheafSnd
    (R : Sheaf K CommRingCat.{max u v})
    (N : SheafOfModules (ringSheaf K R)) {U : Dᵒᵖ}
    (x : (squareZeroSheaf R N).obj.obj U) : N.val.obj U :=
  x.2

/-- The section map obtained by pushing a derivation along the inverse-image
unit. -/
def pushforwardSection (phi : O₁ ⟶ O₂)
    (derivation : Der[(RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).map phi ; M]) {U : Cᵒᵖ}
    (x : O₂.obj.obj U) :
    ((SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M).val.obj U :=
  derivation.d
    (((RingedSite.InverseImage.ringUnit
      (J := J) (K := K) F O₂).hom.app U) x)

/-- Pushing a relative derivation forward preserves addition on sections. -/
theorem pushforwardSection_add (phi : O₁ ⟶ O₂)
    (derivation : Der[(RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).map phi ; M]) {U : Cᵒᵖ}
    (x y : O₂.obj.obj U) :
    pushforwardSection (J := J) (K := K) F phi derivation (x + y) =
      pushforwardSection (J := J) (K := K) F phi derivation x +
        pushforwardSection (J := J) (K := K) F phi derivation y := sorry

/-- Pushing a relative derivation forward preserves the Leibniz rule. -/
theorem pushforwardSection_mul (phi : O₁ ⟶ O₂)
    (derivation : Der[(RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).map phi ; M]) {U : Cᵒᵖ}
    (x y : O₂.obj.obj U) :
    pushforwardSection (J := J) (K := K) F phi derivation (x * y) =
      x • pushforwardSection (J := J) (K := K) F phi derivation y +
        y • pushforwardSection (J := J) (K := K) F phi derivation x := sorry

/-- Pushing a relative derivation forward is natural in the site object. -/
theorem pushforwardSection_naturality (phi : O₁ ⟶ O₂)
    (derivation : Der[(RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).map phi ; M])
    {U V : Cᵒᵖ} (rho : U ⟶ V) (x : O₂.obj.obj U) :
    pushforwardSection (J := J) (K := K) F phi derivation
        (O₂.obj.map rho x) =
      (((SheafOfModules.pushforward
        (RingedSite.InverseImage.structureMap
          (J := J) (K := K) F O₂)).obj M).val.map rho)
        (pushforwardSection (J := J) (K := K) F phi derivation x) := sorry

/-- Pushing a relative derivation forward makes it vanish on the base ring. -/
theorem pushforwardSection_base (phi : O₁ ⟶ O₂)
    (derivation : Der[(RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).map phi ; M]) {U : Cᵒᵖ}
    (x : O₁.obj.obj U) :
    pushforwardSection (J := J) (K := K) F phi derivation
      (phi.hom.app U x) = 0 := sorry

/-- Pushforward transport of a relative derivation along an inverse-image
unit. -/
def pushforward (phi : O₁ ⟶ O₂)
    (derivation : Der[(RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).map phi ; M]) :
    Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M] where
  d {_} := AddMonoidHom.mk'
    (pushforwardSection (J := J) (K := K) F phi derivation)
    (pushforwardSection_add (J := J) (K := K) F phi derivation)
  d_mul := pushforwardSection_mul (J := J) (K := K) F phi derivation
  d_map := pushforwardSection_naturality (J := J) (K := K) F phi derivation
  d_app := pushforwardSection_base (J := J) (K := K) F phi derivation

/-- On sections, a relative derivation determines a morphism to the pushforward
of the corresponding square-zero extension. -/
@[no_expose] def adjointSquareZeroMapApp (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M]) (U : Cᵒᵖ) :
    O₂.obj.obj U ⟶
      (squareZeroSheaf
        ((RingedSite.InverseImage.ringPullback
          (J := J) (K := K) F).obj O₂) M).obj.obj (F.op.obj U) :=
  -- Local instance justification (instance diamond): the square-zero extension uses the right action canonically induced by the commutative left action.
  letI : Module
      (((RingedSite.InverseImage.ringPullback
        (J := J) (K := K) F).obj O₂).obj.obj (F.op.obj U))ᵐᵒᵖ
      (M.val.obj (F.op.obj U)) :=
    oppositeModule _ _
  -- Local instance justification (proof-local temporary data): centrality is needed only to assemble the target square-zero ring structure.
  letI : IsCentralScalar
      (((RingedSite.InverseImage.ringPullback
        (J := J) (K := K) F).obj O₂).obj.obj (F.op.obj U))
      (M.val.obj (F.op.obj U)) := ⟨fun _ _ ↦ rfl⟩
  CommRingCat.ofHom
    { toFun := fun x ↦
        (((RingedSite.InverseImage.ringUnit
          (J := J) (K := K) F O₂).hom.app U) x, derivation.d x)
      map_zero' := by
        ext
        · exact map_zero _
        · exact map_zero _
      map_one' := by
        ext
        · exact map_one _
        · change derivation.d 1 = 0
          exact PresheafOfModules.Derivation.d_one derivation U
      map_add' := by
        intro x y
        ext
        · exact map_add _ _ _
        · exact map_add _ _ _
      map_mul' := by
        intro x y
        ext
        · exact map_mul _ _ _
        · change derivation.d (x * y) =
            x • derivation.d y + y • derivation.d x
          exact derivation.d_mul x y }

/-- A relative derivation determines a morphism of sheaves of rings to the
pushforward of the corresponding square-zero extension. -/
@[no_expose] def adjointSquareZeroMap (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M]) :
    O₂ ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj
      (squareZeroSheaf
        ((RingedSite.InverseImage.ringPullback
          (J := J) (K := K) F).obj O₂) M) :=
  ObjectProperty.homMk
    { app := adjointSquareZeroMapApp (J := J) (K := K) F phi derivation
      naturality := by
        intro U V rho
        ext x
        apply Prod.ext
        · change
            (RingedSite.InverseImage.ringUnit
                (J := J) (K := K) F O₂).hom.app V (O₂.obj.map rho x) =
              ((F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj
                ((RingedSite.InverseImage.ringPullback
                  (J := J) (K := K) F).obj O₂)).obj.map rho
                ((RingedSite.InverseImage.ringUnit
                  (J := J) (K := K) F O₂).hom.app U x)
          simpa using congrArg (fun f ↦ f x)
            ((RingedSite.InverseImage.ringUnit
              (J := J) (K := K) F O₂).hom.naturality rho)
        · change derivation.d (O₂.obj.map rho x) =
            M.val.map (F.op.map rho) (derivation.d x)
          exact derivation.d_map rho x }

/-- The adjoint transpose of the square-zero-extension morphism associated to
a relative derivation. -/
@[no_expose] abbrev squareZeroLift (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M]) :
    (RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).obj O₂ ⟶
      squareZeroSheaf
        ((RingedSite.InverseImage.ringPullback
          (J := J) (K := K) F).obj O₂) M :=
  ((F.sheafAdjunctionContinuous CommRingCat.{max u v} J K).homEquiv _ _).symm
    (adjointSquareZeroMap (J := J) (K := K) F phi derivation)

/-- The section map underlying pullback transport of a relative derivation. -/
def pullbackSection (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M]) {U : Dᵒᵖ}
    (x : ((RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).obj O₂).obj.obj U) : M.val.obj U :=
  squareZeroSheafSnd
    ((RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).obj O₂) M
    ((squareZeroLift (J := J) (K := K) F phi derivation).hom.app U x)

/-- Pullback transport preserves addition on sections. -/
theorem pullbackSection_add (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M]) {U : Dᵒᵖ}
    (x y : ((RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).obj O₂).obj.obj U) :
    pullbackSection (J := J) (K := K) F phi derivation (x + y) =
      pullbackSection (J := J) (K := K) F phi derivation x +
        pullbackSection (J := J) (K := K) F phi derivation y := sorry

/-- Pullback transport satisfies the Leibniz rule. -/
theorem pullbackSection_mul (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M]) {U : Dᵒᵖ}
    (x y : ((RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).obj O₂).obj.obj U) :
    pullbackSection (J := J) (K := K) F phi derivation (x * y) =
      x • pullbackSection (J := J) (K := K) F phi derivation y +
        y • pullbackSection (J := J) (K := K) F phi derivation x := sorry

/-- Pullback transport is natural in the target-site object. -/
theorem pullbackSection_naturality (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M])
    {U V : Dᵒᵖ} (rho : U ⟶ V)
    (x : ((RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).obj O₂).obj.obj U) :
    pullbackSection (J := J) (K := K) F phi derivation
        (((RingedSite.InverseImage.ringPullback
          (J := J) (K := K) F).obj O₂).obj.map rho x) =
      M.val.map rho
        (pullbackSection (J := J) (K := K) F phi derivation x) := sorry

/-- Pullback transport vanishes on the pulled-back base ring. -/
theorem pullbackSection_base (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M]) {U : Dᵒᵖ}
    (x : ((RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).obj O₁).obj.obj U) :
    pullbackSection (J := J) (K := K) F phi derivation
      (((RingedSite.InverseImage.ringPullback
        (J := J) (K := K) F).map phi).hom.app U x) = 0 := sorry

/-- Pullback transport of a relative derivation along inverse image. -/
def pullback (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M]) :
    Der[(RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).map phi ; M] where
  d {_} := AddMonoidHom.mk'
    (pullbackSection (J := J) (K := K) F phi derivation)
    (pullbackSection_add (J := J) (K := K) F phi derivation)
  d_mul := pullbackSection_mul (J := J) (K := K) F phi derivation
  d_map := pullbackSection_naturality (J := J) (K := K) F phi derivation
  d_app := pullbackSection_base (J := J) (K := K) F phi derivation

/-- Pushing forward after pulling back a relative derivation is the identity. -/
theorem pushforward_pullback (phi : O₁ ⟶ O₂)
    (derivation : Der[phi ; (SheafOfModules.pushforward
      (RingedSite.InverseImage.structureMap
        (J := J) (K := K) F O₂)).obj M]) :
    pushforward (J := J) (K := K) F phi
      (pullback (J := J) (K := K) F phi derivation) = derivation := sorry

/-- Pulling back after pushing forward a relative derivation is the identity. -/
theorem pullback_pushforward (phi : O₁ ⟶ O₂)
    (derivation : Der[(RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).map phi ; M]) :
    pullback (J := J) (K := K) F phi
      (pushforward (J := J) (K := K) F phi derivation) = derivation := sorry

/-- Inverse-image transport gives an equivalence between pulled relative
derivations and derivations valued in the corresponding pushforward module. -/
def equiv (phi : O₁ ⟶ O₂) :
    Der[(RingedSite.InverseImage.ringPullback
      (J := J) (K := K) F).map phi ; M] ≃
      Der[phi ; (SheafOfModules.pushforward
        (RingedSite.InverseImage.structureMap
          (J := J) (K := K) F O₂)).obj M] where
  toFun := pushforward (J := J) (K := K) F phi
  invFun := pullback (J := J) (K := K) F phi
  left_inv := pullback_pushforward (J := J) (K := K) F phi
  right_inv := pushforward_pullback (J := J) (K := K) F phi

end SheafOfModules.RelativeDerivation.InverseImage
