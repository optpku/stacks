module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-!
# Picard stack of a morphism of schemes

The category of invertible modules on base changes of `f : X ⟶ S`, bundled as a
stack in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- The hypothesis that every base change `f_T : X_T ⟶ T` has
`O_T ⟶ f_{T,*} O_{X_T}` an isomorphism. -/
class IsIsoBaseChangeStructurePushforward {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- Every base change induces an isomorphism of structure sheaves. -/
  isIso_baseChange :
    ∀ T : Over S, IsIso (pullback.snd f T.hom).commRingSheafPushforwardMap

/-- The identity morphism satisfies the base-change structure-sheaf isomorphism hypothesis. -/
instance instIsIsoBaseChangeStructurePushforwardId {X : Scheme.{u}} :
    IsIsoBaseChangeStructurePushforward (𝟙 X) :=
  sorry

/-- The structure-sheaf map of a base change is an isomorphism under the named hypothesis. -/
instance instIsIsoCommRingSheafPushforwardMap {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIsoBaseChangeStructurePushforward f] (T : Over S) :
    IsIso (pullback.snd f T.hom).commRingSheafPushforwardMap :=
  IsIsoBaseChangeStructurePushforward.isIso_baseChange T

end Scheme.Hom

namespace Picard

/-- An object of the Picard category of `f : X ⟶ S` is an invertible module on a base change. -/
structure Obj {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The test object of `(Sch/S)_fppf`. -/
  base : Over S
  /-- The invertible module on `X_T`. -/
  line : (pullback f base.hom).Modules
  /-- The module is tensor-invertible. -/
  invertible : MonoidalCategory.isInvertibleObject line

/-- Package an invertible module on `X_T` as a Picard object. -/
def ofLine {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    (L : (pullback f T.hom).Modules)
    (hL : MonoidalCategory.isInvertibleObject L) : Obj f where
  base := T
  line := L
  invertible := hL

/-- The test object of `ofLine` is the supplied `S`-scheme. -/
theorem ofLine_base {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    (L : (pullback f T.hom).Modules)
    (hL : MonoidalCategory.isInvertibleObject L) :
    (ofLine f T L hL).base = T :=
  sorry

/-- The module of `ofLine` is the supplied invertible sheaf. -/
theorem ofLine_line {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    (L : (pullback f T.hom).Modules)
    (hL : MonoidalCategory.isInvertibleObject L) :
    (ofLine f T L hL).line = L :=
  sorry

/-- The canonical map `X_T ⟶ X_{T'}` induced by a morphism of test objects over `S`. -/
def baseChangeMap {X S : Scheme.{u}} (f : X ⟶ S) {T T' : Over S} (φ : T ⟶ T') :
    pullback f T.hom ⟶ pullback f T'.hom :=
  pullback.lift (pullback.fst f T.hom) (pullback.snd f T.hom ≫ φ.left)
    (Eq.trans (pullback.condition (f := f) (g := T.hom))
      (Eq.trans (congrArg (fun t => pullback.snd f T.hom ≫ t) φ.w.symm)
        (Category.assoc (pullback.snd f T.hom) φ.left T'.hom).symm))

/-- A morphism of Picard objects is a map of test objects together with an isomorphism of
the pulled-back line bundle. -/
structure Hom {X S : Scheme.{u}} {f : X ⟶ S} (x y : Obj f) where
  /-- The underlying morphism of `S`-schemes. -/
  base : x.base ⟶ y.base
  /-- The induced map of total spaces of the base changes. -/
  schemeMap : pullback f x.base.hom ⟶ pullback f y.base.hom
  /-- `schemeMap` commutes with the projections to `X`. -/
  schemeMap_fst :
    schemeMap ≫ pullback.fst f y.base.hom = pullback.fst f x.base.hom
  /-- `schemeMap` lies over `base` on the test objects. -/
  schemeMap_snd :
    schemeMap ≫ pullback.snd f y.base.hom =
      pullback.snd f x.base.hom ≫ base.left
  /-- The isomorphism `schemeMap^* y.line ≅ x.line`. -/
  iso : (Scheme.Modules.pullback schemeMap).obj y.line ≅ x.line

/-- Build a Picard morphism from a test map, its canonical base change, and a line isomorphism. -/
def homMk {X S : Scheme.{u}} {f : X ⟶ S} {x y : Obj f} (base : x.base ⟶ y.base)
    (iso : (Scheme.Modules.pullback (baseChangeMap f base)).obj y.line ≅ x.line) :
    Hom x y where
  base := base
  schemeMap := baseChangeMap f base
  schemeMap_fst := pullback.lift_fst _ _ _
  schemeMap_snd := pullback.lift_snd _ _ _
  iso := iso

/-- The identity Picard morphism uses the identity of `X_T`. -/
def Hom.id {X S : Scheme.{u}} {f : X ⟶ S} (x : Obj f) : Hom x x where
  base := 𝟙 x.base
  schemeMap := 𝟙 _
  schemeMap_fst := Category.id_comp _
  schemeMap_snd :=
    Eq.trans (Category.id_comp _) (Category.comp_id _).symm
  iso := (Scheme.Modules.pullbackId (pullback f x.base.hom)).app x.line

/-- The line-bundle isomorphism of a composite Picard morphism. -/
def Hom.compIso {X S : Scheme.{u}} {f : X ⟶ S} {x y z : Obj f}
    (α : Hom x y) (β : Hom y z) :
    (Scheme.Modules.pullback (α.schemeMap ≫ β.schemeMap)).obj z.line ≅ x.line :=
  (Scheme.Modules.pullbackComp α.schemeMap β.schemeMap).symm.app z.line ≪≫
    (Scheme.Modules.pullback α.schemeMap).mapIso β.iso ≪≫ α.iso

/-- Composition of Picard morphisms is composition of test maps and of base-change maps. -/
def Hom.compHom {X S : Scheme.{u}} {f : X ⟶ S} {x y z : Obj f}
    (α : Hom x y) (β : Hom y z) : Hom x z where
  base := α.base ≫ β.base
  schemeMap := α.schemeMap ≫ β.schemeMap
  schemeMap_fst := sorry
  schemeMap_snd := sorry
  iso := Hom.compIso α β

/-- Picard objects and their line-bundle isomorphisms form a category. -/
@[reducible] def category {X S : Scheme.{u}} (f : X ⟶ S) : Category (Obj f) where
  Hom := Hom
  id := Hom.id
  comp := fun α β => Hom.compHom α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The projection of the Picard category to `(Sch/S)_fppf`. -/
def p {X S : Scheme.{u}} (f : X ⟶ S) :
    @Functor (Obj f) (category f) (Over S) inferInstance :=
  @CategoryTheory.Functor.mk (Obj f) (category f) (Over S) inferInstance
    (fun x => x.base) (fun {_ _} α => α.base)
    (fun _ => Eq.refl _) (fun {_ _ _} _ _ => Eq.refl _)

/-- The Picard projection is a stack in groupoids on `(Sch/S)_fppf`. -/
theorem p_isStack {X S : Scheme.{u}} (f : X ⟶ S) :
    @IsStack.InGroupoids (Over S) (Obj f) inferInstance (category f)
      (Scheme.fppfTopology.over S) (p f) :=
  sorry

/-- An automorphism of a Picard object lying over the identity of `T` induces an automorphism of
its line bundle. -/
def autOfVertical {X S : Scheme.{u}} {f : X ⟶ S} {x : Obj f} (α : Hom x x)
    (hbase : α.base = 𝟙 x.base) : Aut x.line :=
  α.iso.symm ≪≫
    (Scheme.Modules.pullbackCongr
        (pullback.hom_ext
          (Eq.trans α.schemeMap_fst (Category.id_comp _).symm)
          (Eq.trans α.schemeMap_snd
            (Eq.trans (congrArg (fun k => pullback.snd f x.base.hom ≫ k.left) hbase)
              (Eq.trans (Category.comp_id _) (Category.id_comp _).symm))))).app
      x.line ≪≫
    (Scheme.Modules.pullbackId (pullback f x.base.hom)).app x.line

/-- Automorphisms of an invertible module induce automorphisms of the monoidal unit. -/
def autToAutUnit {X : Scheme.{u}} (L : X.Modules)
    (hL : MonoidalCategory.isInvertibleObject L) (α : Aut L) :
    Aut (𝟙_ X.Modules) :=
  (@MonoidalCategory.isInvertibleObject.tensorInverseIso X.Modules _ _ L hL).conjAut
    ((tensorRight
        (@MonoidalCategory.isInvertibleObject.inverse X.Modules _ _ L hL)).mapIso α)

/-- Automorphisms of the monoidal unit induce automorphisms of an invertible module. -/
def autUnitToAut {X : Scheme.{u}} (L : X.Modules) (β : Aut (𝟙_ X.Modules)) :
    Aut L :=
  (λ_ L).conjAut ((tensorRight L).mapIso β)

/-- The left inverse law of `autToAutUnit`. -/
theorem autToAutUnit_left {X : Scheme.{u}} (L : X.Modules)
    (hL : MonoidalCategory.isInvertibleObject L) (α : Aut L) :
    autUnitToAut L (autToAutUnit L hL α) = α :=
  sorry

/-- The right inverse law of `autToAutUnit`. -/
theorem autToAutUnit_right {X : Scheme.{u}} (L : X.Modules)
    (hL : MonoidalCategory.isInvertibleObject L) (β : Aut (𝟙_ X.Modules)) :
    autToAutUnit L hL (autUnitToAut L β) = β :=
  sorry

/-- Global units of `O_X` act as automorphisms of the structure module. -/
def unitsToAutUnit {X : Scheme.{u}} (u : Γ(X, ⊤)ˣ) :
    Aut (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  Aut.unitsEndEquivAut _
    { val :=
        (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
          (PresheafOfModules.sectionsMk
            (fun U => X.presheaf.map (homOfLE le_top).op (u : Γ(X, ⊤))) sorry)
      inv :=
        (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
          (PresheafOfModules.sectionsMk
            (fun U => X.presheaf.map (homOfLE le_top).op ((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)))
            sorry)
      val_inv := sorry
      inv_val := sorry }

/-- Automorphisms of an invertible module determine global units of `O_X`. -/
def autToUnits {X : Scheme.{u}} (L : X.Modules)
    (hL : MonoidalCategory.isInvertibleObject L) (α : Aut L) : Γ(X, ⊤)ˣ :=
  let αUnit : Aut (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    (RingedSpace.unitIsoTensorUnit X.toRingedSpace).symm.conjAut (autToAutUnit L hL α)
  { val :=
      ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
          (Aut.toEnd _ αUnit)).eval (Opposite.op (⊤ : X.Opens))
    inv :=
      ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
          (Aut.toEnd _ αUnit.symm)).eval (Opposite.op (⊤ : X.Opens))
    val_inv := sorry
    inv_val := sorry }

/-- Global units of `O_X` determine automorphisms of an invertible module. -/
def unitsToAut {X : Scheme.{u}} (L : X.Modules) (u : Γ(X, ⊤)ˣ) : Aut L :=
  autUnitToAut L
    ((RingedSpace.unitIsoTensorUnit X.toRingedSpace).conjAut (unitsToAutUnit u))

/-- The left inverse law of `autToUnits`. -/
theorem autToUnits_left {X : Scheme.{u}} (L : X.Modules)
    (hL : MonoidalCategory.isInvertibleObject L) (α : Aut L) :
    unitsToAut L (autToUnits L hL α) = α :=
  sorry

/-- The right inverse law of `autToUnits`. -/
theorem autToUnits_right {X : Scheme.{u}} (L : X.Modules)
    (hL : MonoidalCategory.isInvertibleObject L) (u : Γ(X, ⊤)ˣ) :
    autToUnits L hL (unitsToAut L u) = u :=
  sorry

end Picard

/-- The Picard stack of a morphism of schemes, as a stack in groupoids over `(Sch/S)_fppf`. -/
def picardStack {X S : Scheme.{u}} (f : X ⟶ S) :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S) :=
  @StackOver.Groupoids.ofProjectionWith (Over S) inferInstance
    (Scheme.fppfTopology.over S) (Picard.Obj f) (Picard.category f)
    (Picard.p f) (Picard.p_isStack f)

/-- The projection of `picardStack f` is the Picard projection to `(Sch/S)_fppf`. -/
theorem picardStack_p {X S : Scheme.{u}} (f : X ⟶ S) :
    (picardStack f).p = Picard.p f :=
  sorry

end AlgebraicGeometry
