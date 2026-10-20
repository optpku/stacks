/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule

/-!
# Solutions of the first-order deformation equation on ringed topoi

Given a first-order thickening `t` of ringed topoi, after identifying underlying topoi of the
target, a morphism `f` of ringed topoi, an `O`-module `G`, and a map `c : f⁻¹J ⟶ G` of
`f⁻¹O_B`-modules, a solution is a first-order thickening of `(Sh(C), O)` together with a
structure map `f⁻¹O_{B'} ⟶ O'` inducing `c`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open Sheaf.InternalModule

noncomputable section

universe u v

namespace RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JC.HasSheafCompose (forget RingCat.{max u v})]
variable [JD.HasSheafCompose (forget RingCat.{max u v})]

/-- Inverse image of a commutative ring sheaf along a morphism of ringed topoi. -/
abbrev inverseImageRing
    {O : Sheaf JC CommRingCat.{max u v}} {OB : Sheaf JD CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (R : Sheaf JD CommRingCat.{max u v}) :
    Sheaf JC RingCat.{max u v} :=
  f.toTopos.ringInverseImage.obj (ringSheaf JD R)

/-- The bottom-row ring map `f⁻¹O_{B'} ⟶ f⁻¹O_B` induced by a first-order thickening `t`. -/
def inverseImageRingMap
    {O : Sheaf JC CommRingCat.{max u v}} {OB OB' : Sheaf JD CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (t : OB' ⟶ OB) :
    inverseImageRing f OB' ⟶ inverseImageRing f OB :=
  f.toTopos.ringInverseImage.map (ringSheafMap t)

variable [JD.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify JD CommRingCat.{max u v}]
variable [JD.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Inverse image `f⁻¹J` of the kernel ideal of a first-order thickening, as an
`f⁻¹O_B`-module. -/
def inverseImageIdeal
    {O : Sheaf JC CommRingCat.{max u v}} {OB OB' : Sheaf JD CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (t : OB' ⟶ OB) [IsFirstOrderThickening t] :
    SheafOfModules.{max u v} (inverseImageRing f OB) :=
  (f.toTopos.moduleInverseImage (ringSheaf JD OB)).obj
    (SheafOfModules.RingedSite.FirstOrderThickening.ideal t)

/-- The type-valued sheaf underlying the unit module of a ring sheaf. -/
def unitCarrierIso {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget RingCat.{max u v})] (R : Sheaf J RingCat.{max u v}) :
    (ToInternal.underlying R).obj (SheafOfModules.unit R) ≅
      (sheafCompose J (forget RingCat.{max u v})).obj R := by
  let A := (ToInternal.underlying R).obj (SheafOfModules.unit R)
  let B := (sheafCompose J (forget RingCat.{max u v})).obj R
  let forward : ∀ U, A.obj.obj U ⟶ B.obj.obj U := fun _ ↦ 𝟙 _
  let backward : ∀ U, B.obj.obj U ⟶ A.obj.obj U := fun _ ↦ 𝟙 _
  let natural : Prop :=
    (∀ U V (k : U ⟶ V), A.obj.map k ≫ forward V = forward U ≫ B.obj.map k) ∧
    (∀ U V (k : U ⟶ V), B.obj.map k ≫ backward V = backward U ≫ A.obj.map k)
  let hom (h : natural) : A ⟶ B :=
    ⟨{ app := forward, naturality := fun U V k ↦ h.1 U V k }⟩
  let inv (h : natural) : B ⟶ A :=
    ⟨{ app := backward, naturality := fun U V k ↦ h.2 U V k }⟩
  have laws : natural ∧ (∀ h : natural,
      hom h ≫ inv h = 𝟙 A ∧ inv h ≫ hom h = 𝟙 B) := by
    sorry
  exact
    { hom := hom laws.1
      inv := inv laws.1
      hom_inv_id := (laws.2 laws.1).1
      inv_hom_id := (laws.2 laws.1).2 }

/-- The type-valued inclusion of the kernel ideal of `t` into `O_{B'}`. -/
def idealCarrierInclusion {OB' OB : Sheaf JD CommRingCat.{max u v}}
    (t : OB' ⟶ OB) [hπ : IsFirstOrderThickening t] :
    (ToInternal.underlying (ringSheaf JD OB)).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal t) ⟶
      (sheafCompose JD (forget RingCat.{max u v})).obj (ringSheaf JD OB') where
  hom :=
    { app := fun U =>
        ↾fun (x : ((ToInternal.underlying (ringSheaf JD OB)).obj
              (SheafOfModules.RingedSite.FirstOrderThickening.ideal t)).obj.obj U) ↦
          KernelIdeal.ιApp t U
            ((hπ.isSquareZero.targetModuleForgetIso inferInstance).hom.hom.app U
              (ToInternal.sectionEquiv (ringSheaf JD OB)
                (SheafOfModules.RingedSite.FirstOrderThickening.ideal t) U x))
      naturality := fun _ _ _ => sorry }

/-- The type-valued inclusion `f⁻¹J ⟶ f⁻¹O_{B'}`. -/
def inverseImageIdealCarrierι
    {O : Sheaf JC CommRingCat.{max u v}} {OB OB' : Sheaf JD CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (t : OB' ⟶ OB) [IsFirstOrderThickening t] :
    (ToInternal.underlying (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      (sheafCompose JC (forget RingCat.{max u v})).obj (inverseImageRing f OB') :=
  (f.toTopos.moduleInverseImageForgetIso (ringSheaf JD OB)).hom.app
      (SheafOfModules.RingedSite.FirstOrderThickening.ideal t) ≫
    f.toTopos.inverseImage.map (idealCarrierInclusion t) ≫
    f.toTopos.ringInverseImageForgetIso.inv.app (ringSheaf JD OB')

variable [JC.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]

/-- The additive inclusion of `f⁻¹J` into the unit of `f⁻¹O_{B'}`. -/
def inverseImageIdeal_toUnit
    {O : Sheaf JC CommRingCat.{max u v}} {OB OB' : Sheaf JD CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (t : OB' ⟶ OB) [IsFirstOrderThickening t] :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      (SheafOfModules.toSheaf (inverseImageRing f OB')).obj
        (SheafOfModules.unit (inverseImageRing f OB')) := by
  let A := (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t)
  let B := (SheafOfModules.toSheaf (inverseImageRing f OB')).obj
    (SheafOfModules.unit (inverseImageRing f OB'))
  let sectionMap (U : Cᵒᵖ) (x : A.obj.obj U) : B.obj.obj U :=
    (unitCarrierIso (inverseImageRing f OB')).inv.hom.app U
      ((inverseImageIdealCarrierι f t).hom.app U
        ((ToInternal.sectionEquiv (inverseImageRing f OB)
          (inverseImageIdeal f t) U).symm x))
  let additive : Prop :=
    (∀ U, sectionMap U 0 = 0) ∧
    (∀ U (x y : A.obj.obj U), sectionMap U (x + y) = sectionMap U x + sectionMap U y)
  let app (h : additive) (U : Cᵒᵖ) : A.obj.obj U ⟶ B.obj.obj U :=
    AddCommGrpCat.ofHom
      { toFun := sectionMap U
        map_zero' := h.1 U
        map_add' := h.2 U }
  have laws : additive ∧ (∀ h : additive, ∀ U V (k : U ⟶ V),
      A.obj.map k ≫ app h V = app h U ≫ B.obj.map k) := by
    sorry
  exact ⟨{ app := app laws.1, naturality := fun U V k ↦ laws.2 laws.1 U V k }⟩

/-- The composite of the inclusion of `f⁻¹J` with the additive map of a structure morphism
`f⁻¹O_{B'} ⟶ O'` is killed by the projection of `π`. -/
theorem kerMap_lift_zero
    {O : Sheaf JC CommRingCat.{max u v}} {OB OB' : Sheaf JD CommRingCat.{max u v}}
    {middle : Sheaf JC CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (t : OB' ⟶ OB) [IsFirstOrderThickening t]
    (π : middle ⟶ O) [IsFirstOrderThickening π]
    (fromInverseImage : inverseImageRing f OB' ⟶ ringSheaf JC middle)
    (hcomm : fromInverseImage ≫ ringSheafMap π =
      inverseImageRingMap f t ≫ f.structureMap) :
    (inverseImageIdeal_toUnit f t ≫
        SheafOfModules.unitUnderlyingMap fromInverseImage) ≫
      (SheafOfModules.toSheaf (ringSheaf JC middle)).map (KernelIdeal.map π) = 0 := sorry

/-- The additive sheaf map `f⁻¹J ⟶ Ker(π)` induced by a commutative square of ring sheaves. -/
def kerMapAdditive
    {O : Sheaf JC CommRingCat.{max u v}} {OB OB' : Sheaf JD CommRingCat.{max u v}}
    {middle : Sheaf JC CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (t : OB' ⟶ OB) [IsFirstOrderThickening t]
    (π : middle ⟶ O) [hπ : IsFirstOrderThickening π]
    (fromInverseImage : inverseImageRing f OB' ⟶ ringSheaf JC middle)
    (hcomm : fromInverseImage ≫ ringSheafMap π =
      inverseImageRingMap f t ≫ f.structureMap) :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      (SheafOfModules.toSheaf (ringSheaf JC O)).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal π) :=
  KernelIdeal.additiveLift π
      (inverseImageIdeal_toUnit f t ≫
        SheafOfModules.unitUnderlyingMap fromInverseImage)
      (kerMap_lift_zero f t π fromInverseImage hcomm) ≫
    (hπ.isSquareZero.targetModuleForgetIso inferInstance).inv

/-- The `f⁻¹O_B`-module map on kernels induced by a commutative square of ring sheaves. -/
def kerMapOf
    {O : Sheaf JC CommRingCat.{max u v}} {OB OB' : Sheaf JD CommRingCat.{max u v}}
    {middle : Sheaf JC CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (t : OB' ⟶ OB) [IsFirstOrderThickening t]
    (π : middle ⟶ O) [hπ : IsFirstOrderThickening π]
    (fromInverseImage : inverseImageRing f OB' ⟶ ringSheaf JC middle)
    (hcomm : fromInverseImage ≫ ringSheafMap π =
      inverseImageRingMap f t ≫ f.structureMap) :
    inverseImageIdeal f t ⟶
      (SheafOfModules.restrictScalars f.structureMap).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal π) where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf JC AddCommGrpCat.{max u v}).map
        (kerMapAdditive f t π fromInverseImage hcomm ≫
          (SheafOfModules.restrictScalarsCompToSheaf f.structureMap).inv.app
            (SheafOfModules.RingedSite.FirstOrderThickening.ideal π)))
      (fun _ _ _ ↦ sorry)

/-- The canonical sequence `0 ⟶ f⁻¹J ⟶ f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ 0` as additive sheaves. -/
def bottomRow
    {O : Sheaf JC CommRingCat.{max u v}} {OB OB' : Sheaf JD CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (t : OB' ⟶ OB) [IsFirstOrderThickening t] :
    ShortComplex (Sheaf JC AddCommGrpCat.{max u v}) :=
  ShortComplex.mk (inverseImageIdeal_toUnit f t)
    (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t)) sorry

/-- The inverse image of the kernel sequence of a first-order thickening is short exact. -/
theorem bottomRow_shortExact
    {O : Sheaf JC CommRingCat.{max u v}} {OB OB' : Sheaf JD CommRingCat.{max u v}}
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
    (t : OB' ⟶ OB) [IsFirstOrderThickening t] :
    (bottomRow f t).ShortExact := sorry

variable {O : Sheaf JC CommRingCat.{max u v}}
variable {OB OB' : Sheaf JD CommRingCat.{max u v}}
variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
variable (G : SheafOfModules.{max u v} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)

/-- A solution of the first-order deformation equation on ringed topoi: a middle ring sheaf
`O'` with a first-order projection onto `O`, a structure map from `f⁻¹O_{B'}`, a kernel
identification with `G`, and the induced map on kernels equal to `c`. -/
structure Solution where
  /-- The unknown middle ring sheaf `O'`. -/
  middle : Sheaf JC CommRingCat.{max u v}
  /-- The square-zero locally surjective projection `O' ⟶ O`. -/
  π : middle ⟶ O
  /-- The projection `O' ⟶ O` is a first-order thickening. -/
  [isFirstOrder : IsFirstOrderThickening π]
  /-- The inverse-image structure map `(f')♯ : f⁻¹O_{B'} ⟶ O'`. -/
  fromInverseImage : inverseImageRing f OB' ⟶ ringSheaf JC middle
  /-- The right-hand square of ring sheaves commutes. -/
  comm : fromInverseImage ≫ ringSheafMap π = inverseImageRingMap f t ≫ f.structureMap
  /-- Identification of `Ker(π)` with `G` as `O`-modules. -/
  kernelIso : SheafOfModules.RingedSite.FirstOrderThickening.ideal π ≅ G
  /-- The induced map on kernels equals `c`. -/
  induces :
    kerMapOf f t π fromInverseImage comm ≫
      (SheafOfModules.restrictScalars f.structureMap).map kernelIso.hom = c

namespace Solution

/-- Assemble a solution from a middle ring sheaf, its structure maps, a kernel identification,
and the induced-map condition. -/
def of (middle : Sheaf JC CommRingCat.{max u v}) (π : middle ⟶ O)
    [isFirstOrder : IsFirstOrderThickening π]
    (fromInverseImage : inverseImageRing f OB' ⟶ ringSheaf JC middle)
    (comm : fromInverseImage ≫ ringSheafMap π = inverseImageRingMap f t ≫ f.structureMap)
    (kernelIso : SheafOfModules.RingedSite.FirstOrderThickening.ideal π ≅ G)
    (induces :
      kerMapOf f t π fromInverseImage comm ≫
        (SheafOfModules.restrictScalars f.structureMap).map kernelIso.hom = c) :
    Solution t f G c where
  middle := middle
  π := π
  isFirstOrder := isFirstOrder
  fromInverseImage := fromInverseImage
  comm := comm
  kernelIso := kernelIso
  induces := induces

variable {t f G c}

/-- The `f⁻¹O_B`-module map on kernels induced by a solution. -/
def kerMap (S : Solution t f G c) :
    inverseImageIdeal f t ⟶
      (SheafOfModules.restrictScalars f.structureMap).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal S.π
          (hπ := S.isFirstOrder)) :=
  kerMapOf f t S.π (hπ := S.isFirstOrder) S.fromInverseImage S.comm

/-- A solution is a first-order thickening of `O` whose structure map from `f⁻¹O_{B'}`
commutes with `t` and `f` and induces `c` on kernels. -/
theorem spec (S : Solution t f G c) :
    S.fromInverseImage ≫ ringSheafMap S.π =
        inverseImageRingMap f t ≫ f.structureMap ∧
      S.kerMap ≫
          (SheafOfModules.restrictScalars f.structureMap).map S.kernelIso.hom = c := sorry

/-- The identification of kernels induces the given map `c`. -/
theorem induces_eq (S : Solution t f G c) :
    S.kerMap ≫ (SheafOfModules.restrictScalars f.structureMap).map S.kernelIso.hom = c :=
  sorry

/-- The top row `0 ⟶ Ker(π) ⟶ O' ⟶ O ⟶ 0` of additive sheaves. -/
abbrev topRow (S : Solution t f G c) :
    ShortComplex (Sheaf JC AddCommGrpCat.{max u v}) :=
  KernelIdeal.underlyingShortComplex S.π

/-- The top row of a solution is short exact. -/
theorem exact_top (S : Solution t f G c) : (topRow S).ShortExact := sorry

end Solution

end RingedSite.FirstOrderThickening
