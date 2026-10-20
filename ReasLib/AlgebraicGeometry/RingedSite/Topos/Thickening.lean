module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module

/-!
# Thickenings of ringed topoi

A morphism of ringed topoi is a thickening when its direct image is an equivalence of
underlying topoi, the structure-sheaf map is locally surjective, and its kernel is locally nilpotent.
A first-order thickening is a thickening whose kernel is square zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.ChangeOfRings

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{w}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The unit-module form of `i^♯ : 𝒪_Y ⟶ i_* 𝒪_X` on the target site. -/
noncomputable def kernelMap (f : ToposHom X Y) :
    SheafOfModules.unit Y.structureSheaf ⟶
      (SheafOfModules.pushforward (homOverId f.directStructureMap)).obj
        (SheafOfModules.unit (f.toTopos.ringDirectImage.obj X.structureSheaf)) :=
  SheafOfModules.unitToPushforwardObjUnit (homOverId f.directStructureMap)

/-- The kernel ideal `ℐ = Ker(i^♯)` of a morphism of ringed topoi, as an `𝒪_Y`-module. -/
noncomputable def kernelIdeal (f : ToposHom X Y) :
    SheafOfModules.{w} Y.structureSheaf :=
  kernel (kernelMap f)

/-- Abbreviation for the kernel ideal of a morphism of ringed topoi. -/
noncomputable abbrev ker (f : ToposHom X Y) : SheafOfModules.{w} Y.structureSheaf :=
  kernelIdeal f

/-- The canonical inclusion of `Ker(i^♯)` into the unit `𝒪_Y`-module. -/
noncomputable def kernelIdeal_ι (f : ToposHom X Y) :
    kernelIdeal f ⟶ SheafOfModules.unit Y.structureSheaf :=
  kernel.ι (kernelMap f)

/-- The kernel-ideal inclusion followed by `i^♯` is zero. -/
theorem kernelIdeal_ι_comp_kernelMap (f : ToposHom X Y) :
    kernelIdeal_ι f ≫ kernelMap f = 0 := sorry

/-- A local section of `Ker(i^♯)` is locally nilpotent after restriction along some covering
sieve. -/
def IsLocallyNilpotent (f : ToposHom X Y) : Prop :=
  ∀ (U : Y.carrier) (s : Y.structureSheaf.obj.obj (op U)),
    (f.directStructureMap.hom.app (op U)).hom s = 0 →
      ∃ S : Sieve U, S ∈ Y.siteTopology U ∧
        ∀ {V : Y.carrier} {h : V ⟶ U}, S h →
          IsNilpotent ((Y.structureSheaf.obj.map h.op).hom s)

/-- Local nilpotence of `Ker(i^♯)` is covering-local nilpotence of kernel sections of `i^♯`. -/
theorem isLocallyNilpotent_iff (f : ToposHom X Y) :
    IsLocallyNilpotent f ↔
      ∀ (U : Y.carrier) (s : Y.structureSheaf.obj.obj (op U)),
        (f.directStructureMap.hom.app (op U)).hom s = 0 →
          ∃ S : Sieve U, S ∈ Y.siteTopology U ∧
            ∀ {V : Y.carrier} {h : V ⟶ U}, S h →
              IsNilpotent ((Y.structureSheaf.obj.map h.op).hom s) := sorry

/-- The kernel of `i^♯` is square zero sectionwise. -/
def kernel_isSquareZero (f : ToposHom X Y) : Prop :=
  ∀ U : Y.carrierᵒᵖ, RingHom.ker (f.directStructureMap.hom.app U).hom ^ 2 = ⊥

/-- Square-zeroness of `Ker(i^♯)` is sectionwise vanishing of products in the kernel ideal. -/
theorem kernel_isSquareZero_iff (f : ToposHom X Y) :
    kernel_isSquareZero f ↔
      ∀ U : Y.carrierᵒᵖ, RingHom.ker (f.directStructureMap.hom.app U).hom ^ 2 = ⊥ := sorry

/-- A morphism of ringed topoi is a thickening when `i_*` is an equivalence, `i^♯` is locally
surjective, and `Ker(i^♯)` is locally nilpotent. -/
class IsThickening (f : ToposHom X Y) : Prop where
  /-- Direct image of underlying topoi is an equivalence. -/
  [pushforward_isEquivalence : Functor.IsEquivalence f.toTopos.pushforward]
  /-- The structure-sheaf map `i^♯ : 𝒪_Y ⟶ i_* 𝒪_X` is locally surjective. -/
  [directStructureMap_isLocallySurjective : Sheaf.IsLocallySurjective f.directStructureMap]
  /-- The kernel of `i^♯` is a locally nilpotent sheaf of ideals. -/
  kernel_isLocallyNilpotent : IsLocallyNilpotent f

attribute [instance] IsThickening.pushforward_isEquivalence
attribute [instance] IsThickening.directStructureMap_isLocallySurjective

/-- A morphism of ringed topoi is a thickening iff its direct image is an equivalence, its
structure-sheaf map is locally surjective, and its kernel is locally nilpotent. -/
theorem isThickening_iff (f : ToposHom X Y) :
    IsThickening f ↔
      Functor.IsEquivalence f.toTopos.pushforward ∧
        Sheaf.IsLocallySurjective f.directStructureMap ∧
          IsLocallyNilpotent f := sorry

/-- A first-order thickening of ringed topoi is a thickening whose kernel ideal is square
zero. -/
class IsFirstOrderThickening (f : ToposHom X Y) : Prop extends IsThickening f where
  /-- The kernel of `i^♯` has square zero. -/
  kernel_squareZero : kernel_isSquareZero f

/-- A morphism of ringed topoi is a first-order thickening iff it is a thickening and its
kernel ideal is square zero. -/
theorem isFirstOrderThickening_iff (f : ToposHom X Y) :
    IsFirstOrderThickening f ↔ IsThickening f ∧ kernel_isSquareZero f := sorry

/-- The kernel ideal of a first-order thickening, viewed as an `𝒪_X`-module by inverse
image. -/
noncomputable def idealModule (f : ToposHom X Y) [IsFirstOrderThickening f]
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    SheafOfModules.{w} X.structureSheaf :=
  f.modulePullback.obj (kernelIdeal f)

/-- Inverse image recovers the kernel ideal of a first-order thickening as an `𝒪_X`-module. -/
theorem idealModule_eq (f : ToposHom X Y) [IsFirstOrderThickening f]
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    idealModule f = f.modulePullback.obj (kernelIdeal f) := sorry

end RingedSite.ToposHom
