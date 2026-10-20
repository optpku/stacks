/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Strict
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.FlatOver

/-!
# Flat morphism squares of first-order thickenings of ringed topoi

A commutative square of first-order thickenings over a morphism of ringed topoi carries
strict restriction squares, flat thickened vertical morphisms, and a relatively flat module.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe uC vC uB vB uC1 vC1 uC2 vC2 uB1 vB1 uB2 vB2 w

namespace RingedSite.ToposHom.Thickening

variable {C : Type uC} [Category.{vC} C]
variable {B : Type uB} [Category.{vB} B]
variable {C1 : Type uC1} [Category.{vC1} C1]
variable {C2 : Type uC2} [Category.{vC2} C2]
variable {B1 : Type uB1} [Category.{vB1} B1]
variable {B2 : Type uB2} [Category.{vB2} B2]
variable {JC : GrothendieckTopology C}
variable {JB : GrothendieckTopology B}
variable {JC1 : GrothendieckTopology C1}
variable {JC2 : GrothendieckTopology C2}
variable {JB1 : GrothendieckTopology B1}
variable {JB2 : GrothendieckTopology B2}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC1.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC2.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB1.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB2.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC.HasSheafCompose (forget RingCat.{w})]
variable [JB.HasSheafCompose (forget RingCat.{w})]
variable [JC1.HasSheafCompose (forget RingCat.{w})]
variable [JC2.HasSheafCompose (forget RingCat.{w})]
variable [JB1.HasSheafCompose (forget RingCat.{w})]
variable [JB2.HasSheafCompose (forget RingCat.{w})]
variable [JC.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JB.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JC1.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JC2.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JB1.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JB2.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JC1 AddCommGrpCat.{w}]
variable [JC1.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify JC2 AddCommGrpCat.{w}]
variable [JC2.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify JB1 AddCommGrpCat.{w}]
variable [JB1.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify JB2 AddCommGrpCat.{w}]
variable [JB2.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf JC CommRingCat.{w}}
variable {O_B : Sheaf JB CommRingCat.{w}}
variable {O1' : Sheaf JC1 CommRingCat.{w}}
variable {O2' : Sheaf JC2 CommRingCat.{w}}
variable {OB1' : Sheaf JB1 CommRingCat.{w}}
variable {OB2' : Sheaf JB2 CommRingCat.{w}}

/-- A commutative square of first-order thickenings over a morphism of ringed topoi,
with strict restriction squares, flat thickened vertical morphisms, and a module on the
unthickened source flat over the unthickened base. -/
structure FlatMorphismSquare
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JB O_B))
    (i1 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC1 O1'))
    (i2 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC2 O2'))
    (t1 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB1 OB1'))
    (t2 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB2 OB2'))
    (f1' : ToposHom (ofCommRingSheaf JC1 O1') (ofCommRingSheaf JB1 OB1'))
    (f2' : ToposHom (ofCommRingSheaf JC2 O2') (ofCommRingSheaf JB2 OB2'))
    [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
    [IsFirstOrderThickening t1] [IsFirstOrderThickening t2]
    [(SheafOfModules.restrictScalars.{w} f1'.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} f2'.structureMap).IsRightAdjoint] where
  /-- The horizontal morphism between the source thickenings. -/
  h : ToposHom (ofCommRingSheaf JC1 O1') (ofCommRingSheaf JC2 O2')
  /-- The horizontal morphism between the base thickenings. -/
  base : ToposHom (ofCommRingSheaf JB1 OB1') (ofCommRingSheaf JB2 OB2')
  /-- The upper horizontal morphism lies over the unthickened source. -/
  over_source : TwoIso (i1.comp h) i2
  /-- The lower horizontal morphism lies over the unthickened base. -/
  over_base : TwoIso (t1.comp base) t2
  /-- The first thickened vertical morphism restricts to the given morphism. -/
  comm1 : TwoIso (i1.comp f1') (f.comp t1)
  /-- The second thickened vertical morphism restricts to the given morphism. -/
  comm2 : TwoIso (i2.comp f2') (f.comp t2)
  /-- The square of thickened morphisms commutes. -/
  comm_thick : TwoIso (h.comp f2') (f1'.comp base)
  /-- The two pastings from the source composite to the base composite agree. -/
  coherence : (Functor.whiskerRight over_source.homIso.hom f2'.toTopos.pushforward) ≫
        comm2.homIso.hom =
      (Functor.associator i1.toTopos.pushforward h.toTopos.pushforward
        f2'.toTopos.pushforward).hom ≫
      Functor.whiskerLeft i1.toTopos.pushforward comm_thick.homIso.hom ≫
      (Functor.associator i1.toTopos.pushforward f1'.toTopos.pushforward
        base.toTopos.pushforward).inv ≫
      Functor.whiskerRight comm1.homIso.hom base.toTopos.pushforward ≫
      (Functor.associator f.toTopos.pushforward t1.toTopos.pushforward
        base.toTopos.pushforward).hom ≫
      Functor.whiskerLeft f.toTopos.pushforward over_base.homIso.hom
  /-- The first restriction square is strict. -/
  strict1 : @IsStrict _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (homMk i1 f f1' t1 comm1)
      (inferInstanceAs (IsThickening i1))
      (inferInstanceAs (IsThickening t1))
      (inferInstanceAs
        ((SheafOfModules.restrictScalars.{w} f1'.structureMap).IsRightAdjoint))
  /-- The second restriction square is strict. -/
  strict2 : @IsStrict _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (homMk i2 f f2' t2 comm2)
      (inferInstanceAs (IsThickening i2))
      (inferInstanceAs (IsThickening t2))
      (inferInstanceAs
        ((SheafOfModules.restrictScalars.{w} f2'.structureMap).IsRightAdjoint))
  /-- The first thickened vertical morphism is flat. -/
  flat1 : ToposHom.IsFlat f1'
  /-- The second thickened vertical morphism is flat. -/
  flat2 : ToposHom.IsFlat f2'
  /-- A module on the unthickened source. -/
  module : ringedSiteModuleCategory.{uC, vC, w, w} JC O
  /-- The module is flat over the unthickened base. -/
  module_isFlatOver : IsFlatOver f module

namespace FlatMorphismSquare

variable {f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JB O_B)}
variable {i1 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC1 O1')}
variable {i2 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC2 O2')}
variable {t1 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB1 OB1')}
variable {t2 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB2 OB2')}
variable {f1' : ToposHom (ofCommRingSheaf JC1 O1') (ofCommRingSheaf JB1 OB1')}
variable {f2' : ToposHom (ofCommRingSheaf JC2 O2') (ofCommRingSheaf JB2 OB2')}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening t1] [IsFirstOrderThickening t2]
variable [(SheafOfModules.restrictScalars.{w} f1'.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} f2'.structureMap).IsRightAdjoint]

/-- Assemble a flat square of first-order thickenings from the horizontal morphisms,
comparison cells, strictness and flatness witnesses, and a relatively flat module. -/
def of
    (h : ToposHom (ofCommRingSheaf JC1 O1') (ofCommRingSheaf JC2 O2'))
    (base : ToposHom (ofCommRingSheaf JB1 OB1') (ofCommRingSheaf JB2 OB2'))
    (over_source : TwoIso (i1.comp h) i2)
    (over_base : TwoIso (t1.comp base) t2)
    (comm1 : TwoIso (i1.comp f1') (f.comp t1))
    (comm2 : TwoIso (i2.comp f2') (f.comp t2))
    (comm_thick : TwoIso (h.comp f2') (f1'.comp base))
    (coherence : (Functor.whiskerRight over_source.homIso.hom f2'.toTopos.pushforward) ≫
        comm2.homIso.hom =
      (Functor.associator i1.toTopos.pushforward h.toTopos.pushforward
        f2'.toTopos.pushforward).hom ≫
      Functor.whiskerLeft i1.toTopos.pushforward comm_thick.homIso.hom ≫
      (Functor.associator i1.toTopos.pushforward f1'.toTopos.pushforward
        base.toTopos.pushforward).inv ≫
      Functor.whiskerRight comm1.homIso.hom base.toTopos.pushforward ≫
      (Functor.associator f.toTopos.pushforward t1.toTopos.pushforward
        base.toTopos.pushforward).hom ≫
      Functor.whiskerLeft f.toTopos.pushforward over_base.homIso.hom)
    (strict1 : @IsStrict _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (homMk i1 f f1' t1 comm1)
      (inferInstanceAs (IsThickening i1))
      (inferInstanceAs (IsThickening t1))
      (inferInstanceAs
        ((SheafOfModules.restrictScalars.{w} f1'.structureMap).IsRightAdjoint)))
    (strict2 : @IsStrict _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (homMk i2 f f2' t2 comm2)
      (inferInstanceAs (IsThickening i2))
      (inferInstanceAs (IsThickening t2))
      (inferInstanceAs
        ((SheafOfModules.restrictScalars.{w} f2'.structureMap).IsRightAdjoint)))
    (flat1 : ToposHom.IsFlat f1') (flat2 : ToposHom.IsFlat f2')
    (F : ringedSiteModuleCategory.{uC, vC, w, w} JC O)
    (module_isFlatOver : IsFlatOver f F) : FlatMorphismSquare f i1 i2 t1 t2 f1' f2' where
  h := h
  base := base
  over_source := over_source
  over_base := over_base
  comm1 := comm1
  comm2 := comm2
  comm_thick := comm_thick
  coherence := coherence
  strict1 := strict1
  strict2 := strict2
  flat1 := flat1
  flat2 := flat2
  module := F
  module_isFlatOver := module_isFlatOver

/-- Both restriction squares are strict, both thickened vertical morphisms are flat,
and the stored module is flat over the unthickened base. -/
theorem spec (S : FlatMorphismSquare f i1 i2 t1 t2 f1' f2') :
    @IsStrict _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (homMk i1 f f1' t1 S.comm1)
      (inferInstanceAs (IsThickening i1))
      (inferInstanceAs (IsThickening t1))
      (inferInstanceAs
        ((SheafOfModules.restrictScalars.{w} f1'.structureMap).IsRightAdjoint)) ∧
      @IsStrict _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (homMk i2 f f2' t2 S.comm2)
      (inferInstanceAs (IsThickening i2))
      (inferInstanceAs (IsThickening t2))
      (inferInstanceAs
        ((SheafOfModules.restrictScalars.{w} f2'.structureMap).IsRightAdjoint)) ∧
        ToposHom.IsFlat f1' ∧ ToposHom.IsFlat f2' ∧ IsFlatOver f S.module :=
  ⟨S.strict1, S.strict2, S.flat1, S.flat2, S.module_isFlatOver⟩

end FlatMorphismSquare

end RingedSite.ToposHom.Thickening
