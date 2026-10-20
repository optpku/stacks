module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.Solution
public import stacks_project.Chap91.Remark_91_10_10_Thickening

open CategoryTheory
open SheafOfModules.RingedSite
open RingedSite.FirstOrderThickening

universe u v

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JC.HasSheafCompose (forget RingCat.{max u v})]
variable [JD.HasSheafCompose (forget RingCat.{max u v})]

variable [JD.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify JD CommRingCat.{max u v}]
variable [JD.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable [JC.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable {O : Sheaf JC CommRingCat.{max u v}}
variable {OB OB' : Sheaf JD CommRingCat.{max u v}}
variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : RingedSite.ToposHom (RingedSite.ofCommRingSheaf JC O)
  (RingedSite.ofCommRingSheaf JD OB))
variable (G : SheafOfModules.{max u v} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)

#check (RingedSite.FirstOrderThickening.Solution.spec :
  (S : RingedSite.FirstOrderThickening.Solution t f G c) →
    S.fromInverseImage ≫ ringSheafMap S.π = inverseImageRingMap f t ≫ f.structureMap ∧
      S.kerMap ≫ (SheafOfModules.restrictScalars f.structureMap).map S.kernelIso.hom = c)

end
