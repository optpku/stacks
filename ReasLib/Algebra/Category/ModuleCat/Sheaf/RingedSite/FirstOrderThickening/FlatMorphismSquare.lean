module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.KernelMap

/-!
# Flat morphism squares of first-order thickenings

A flat morphism square is a commutative square of same-site first-order
thickenings along `f : O_B ⟶ O`, with both thickened maps
restricting to `f`, both pairs strict, both thickened maps flat, and an `O`-module
flat over `O_B`.

Strictness is epimorphicity of the pullback comparison
`(extendScalars (ringSheafMap f)).obj (ideal τ) ⟶ ideal π`, the
`extendRestrictHomEquiv` mate of the canonical adjunct kernel map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}

/-- The comparison `f^* J ⟶ I` of descended kernel ideals as `O`-modules, obtained as
the extension-of-scalars mate of `inducedKernelMap`. -/
noncomputable def kernelPullbackMap {π : O' ⟶ O} {τ : OB' ⟶ OB}
    [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
    (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
    (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f) :
    (extendScalars (ringSheafMap f)).obj (ideal τ) ⟶ ideal π :=
  (extendRestrictHomEquiv (ringSheafMap f) (ideal τ) (ideal π)).symm
    (inducedKernelMap τ f π f' hcomm)

/-- The adjunct of `kernelPullbackMap` recovers `inducedKernelMap`. -/
theorem kernelPullbackMap_adjunct {π : O' ⟶ O} {τ : OB' ⟶ OB}
    [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
    (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
    (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f) :
    extendRestrictHomEquiv (ringSheafMap f) (ideal τ) (ideal π)
        (kernelPullbackMap f f' hcomm) =
      inducedKernelMap τ f π f' hcomm := sorry

/-- A morphism of first-order thickenings is strict when the comparison `f^* J ⟶ I`
of descended kernel ideals is an epimorphism of `O`-modules. -/
def IsStrict {π : O' ⟶ O} {τ : OB' ⟶ OB}
    [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
    (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
    (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f) : Prop :=
  Epi (kernelPullbackMap f f' hcomm)

/-- Strictness is epimorphicity of the pullback comparison of kernel ideals. -/
theorem isStrict_iff {π : O' ⟶ O} {τ : OB' ⟶ OB}
    [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
    (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
    (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f) :
    IsStrict f f' hcomm ↔ Epi (kernelPullbackMap f f' hcomm) := sorry

/-- A commutative square of first-order thickenings along a same-site morphism
`f : O_B ⟶ O`, with both thickened maps restricting to `f`, both pairs strict, both
thickened maps flat, and an `O`-module flat over `O_B`. -/
structure FlatMorphismSquare
    {O O_B O1' O2' OB1' OB2' : Sheaf J CommRingCat.{max u v}}
    (f : O_B ⟶ O) (π1 : O1' ⟶ O) (π2 : O2' ⟶ O)
    (τ1 : OB1' ⟶ O_B) (τ2 : OB2' ⟶ O_B)
    [IsFirstOrderThickening π1] [IsFirstOrderThickening π2]
    [IsFirstOrderThickening τ1] [IsFirstOrderThickening τ2]
    [(restrictScalars (ringSheafMap f)).IsRightAdjoint] where
  /-- The morphism `h` of first-order thickenings of `O`. -/
  h : Hom π1 π2
  /-- The morphism of first-order thickenings of `O_B`. -/
  base : Hom τ1 τ2
  /-- The thickened structure map `f'_1`. -/
  f1' : OB1' ⟶ O1'
  /-- The thickened structure map `f'_2`. -/
  f2' : OB2' ⟶ O2'
  /-- The pair `(f, f'_1)` restricts to `f`. -/
  comm1 : f1' ≫ π1 = τ1 ≫ f
  /-- The pair `(f, f'_2)` restricts to `f`. -/
  comm2 : f2' ≫ π2 = τ2 ≫ f
  /-- The thickened ring-sheaf square commutes. -/
  comm_thick : f2' ≫ h.hom = base.hom ≫ f1'
  /-- The pair `(f, f'_1)` is a strict morphism of thickenings. -/
  strict1 : IsStrict f f1' comm1
  /-- The pair `(f, f'_2)` is a strict morphism of thickenings. -/
  strict2 : IsStrict f f2' comm2
  /-- The morphism `f'_1` is flat. -/
  flat1 : IsFlatHom f1'
  /-- The morphism `f'_2` is flat. -/
  flat2 : IsFlatHom f2'
  /-- The `O`-module `F`. -/
  module : ringedSiteModuleCategory.{u, v, max u v, max u v} J O
  /-- The module `F` is flat over `O_B`. -/
  module_isFlatOver : IsFlat O_B ((restrictionAlong f).obj module)

namespace FlatMorphismSquare

variable {O O_B O1' O2' OB1' OB2' : Sheaf J CommRingCat.{max u v}}
variable {f : O_B ⟶ O} {π1 : O1' ⟶ O} {π2 : O2' ⟶ O}
variable {τ1 : OB1' ⟶ O_B} {τ2 : OB2' ⟶ O_B}
variable [IsFirstOrderThickening π1] [IsFirstOrderThickening π2]
variable [IsFirstOrderThickening τ1] [IsFirstOrderThickening τ2]
variable [(restrictScalars (ringSheafMap f)).IsRightAdjoint]

/-- Assemble a flat morphism square from its ring-sheaf maps, thickening morphisms,
commutativities, strictness and flatness witnesses, and the stored module. -/
def of (h : Hom π1 π2) (base : Hom τ1 τ2) (f1' : OB1' ⟶ O1') (f2' : OB2' ⟶ O2')
    (comm1 : f1' ≫ π1 = τ1 ≫ f) (comm2 : f2' ≫ π2 = τ2 ≫ f)
    (comm_thick : f2' ≫ h.hom = base.hom ≫ f1')
    (strict1 : IsStrict f f1' comm1) (strict2 : IsStrict f f2' comm2)
    (flat1 : IsFlatHom f1') (flat2 : IsFlatHom f2')
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O)
    (module_isFlatOver : IsFlat O_B ((restrictionAlong f).obj F)) :
    FlatMorphismSquare f π1 π2 τ1 τ2 where
  h := h
  base := base
  f1' := f1'
  f2' := f2'
  comm1 := comm1
  comm2 := comm2
  comm_thick := comm_thick
  strict1 := strict1
  strict2 := strict2
  flat1 := flat1
  flat2 := flat2
  module := F
  module_isFlatOver := module_isFlatOver

/-- Both restriction squares commute. -/
theorem restricts (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    CommSq S.f1' τ1 π1 f ∧ CommSq S.f2' τ2 π2 f := sorry

/-- The thickened ring-sheaf square commutes. -/
theorem thickenedSq (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    CommSq S.f2' S.base.hom S.h.hom S.f1' := sorry

/-- Both pairs `(f, f'_i)` are strict, both `f'_i` are flat, and the stored module is
flat over `O_B`. -/
theorem spec (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    IsStrict f S.f1' S.comm1 ∧ IsStrict f S.f2' S.comm2 ∧
      IsFlatHom S.f1' ∧ IsFlatHom S.f2' ∧
      IsFlat O_B ((restrictionAlong f).obj S.module) := sorry

/-- The comparison `f^* J_1 ⟶ I_1` of descended kernel ideals as `O`-modules. -/
noncomputable def idealMap_fst (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    (extendScalars (ringSheafMap f)).obj (ideal τ1) ⟶ ideal π1 :=
  kernelPullbackMap f S.f1' S.comm1

/-- The comparison `f^* J_2 ⟶ I_2` of descended kernel ideals as `O`-modules. -/
noncomputable def idealMap_snd (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    (extendScalars (ringSheafMap f)).obj (ideal τ2) ⟶ ideal π2 :=
  kernelPullbackMap f S.f2' S.comm2

end FlatMorphismSquare

end SheafOfModules.RingedSite.FirstOrderThickening
