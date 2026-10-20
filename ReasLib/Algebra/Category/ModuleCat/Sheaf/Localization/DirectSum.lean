module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Extension of module sheaves from a slice by direct sums

Extension from a slice is the sheafification of the presheaf whose sections
are sums indexed by arrows into the localizing object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w z

namespace SheafOfModules.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

set_option backward.isDefEq.respectTransparency false in
/-- Extension of a module sheaf on the slice to a presheaf, with sections at
an object given by the direct sum over arrows into the localizing object. -/
def lowerShriekPresheafDirectSum (R : Sheaf J RingCat.{w}) (U : C)
    [UnivLE.{v, z}] :
    SheafOfModules.{z} (R.over U) ⥤ PresheafOfModules.{z} R.obj where
  obj G :=
    { obj V := ∐ fun arrow : V.unop ⟶ U ↦ G.val.obj (op (Over.mk arrow))
      map {V W} restriction := Limits.Sigma.desc fun arrow ↦
        G.val.map (Over.homMk
          (U := Over.mk (restriction.unop ≫ arrow)) (V := Over.mk arrow)
          restriction.unop (by rfl)).op ≫
          (ModuleCat.restrictScalars (R.obj.map restriction).hom).map
            (Limits.Sigma.ι (C := ModuleCat.{z} (R.obj.obj W))
              (fun lift : W.unop ⟶ U ↦ G.val.obj (op (Over.mk lift)))
              (restriction.unop ≫ arrow))
      map_id := sorry
      map_comp := sorry }
  map {G H} morphism :=
    { app V := Limits.Sigma.desc (C := ModuleCat.{z} (R.obj.obj V))
        (f := fun arrow : V.unop ⟶ U ↦
          (G.val.obj (op (Over.mk arrow)) : ModuleCat.{z} (R.obj.obj V)))
        fun arrow ↦
        morphism.val.app (op (Over.mk arrow)) ≫
          Limits.Sigma.ι (C := ModuleCat.{z} (R.obj.obj V))
            (fun lift : V.unop ⟶ U ↦
              (H.val.obj (op (Over.mk lift)) : ModuleCat.{z} (R.obj.obj V))) arrow
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Extension from the slice is obtained by sheafifying the arrow-indexed
direct-sum presheaf. -/
def lowerShriekDirectSum (R : Sheaf J RingCat.{w}) (U : C)
    [UnivLE.{v, z}] [HasWeakSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    SheafOfModules.{z} (R.over U) ⥤ SheafOfModules.{z} R :=
  lowerShriekPresheafDirectSum R U ⋙
    PresheafOfModules.sheafification (𝟙 R.obj)

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified direct-sum extension is left adjoint to restriction to the
slice; its Hom correspondence is evaluation on the summands and restriction
along the slice arrows. -/
def lowerShriekDirectSumAdjunction (R : Sheaf J RingCat.{w}) (U : C)
    [UnivLE.{v, z}] [HasWeakSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    lowerShriekDirectSum R U ⊣ SheafOfModules.overFunctor R U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G F ↦
        { toFun := fun morphism ↦
            { val :=
                { app V := ModuleCat.ofHom
                    { toFun := fun element ↦
                        (PresheafOfModules.sheafificationHomEquiv
                          (𝟙 R.obj) morphism).app (op V.unop.left)
                          (Limits.Sigma.ι
                            (C := ModuleCat.{z} (R.obj.obj (op V.unop.left)))
                            (fun arrow : V.unop.left ⟶ U ↦
                              G.val.obj (op (Over.mk arrow))) V.unop.hom element)
                      map_add' := sorry
                      map_smul' := sorry }
                  naturality := sorry } }
          invFun := fun morphism ↦
            (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
              { app V := by
                  exact Limits.Sigma.desc (C := ModuleCat.{z} (R.obj.obj V))
                    (f := fun arrow : V.unop ⟶ U ↦
                      (G.val.obj (op (Over.mk arrow)) : ModuleCat.{z} (R.obj.obj V)))
                    fun arrow ↦ morphism.val.app (op (Over.mk arrow))
                naturality := sorry }
          left_inv := sorry
          right_inv := sorry }
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Evaluation of extension identifies it with the sheafification of the
arrow-indexed direct-sum presheaf. -/
theorem lowerShriekDirectSum_obj (R : Sheaf J RingCat.{w}) (U : C)
    [UnivLE.{v, z}] [HasWeakSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    (G : SheafOfModules.{z} (R.over U)) :
    (lowerShriekDirectSum R U).obj G =
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((lowerShriekPresheafDirectSum R U).obj G) := rfl

end SheafOfModules.Localization
