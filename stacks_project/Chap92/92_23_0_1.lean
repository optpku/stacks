/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.Solution
import StacksCheckRecall

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

/- 92.23.0.1: given a first-order thickening t of ringed topoi with J = Ker(t♯),
a morphism f : (Sh(C), O) ⟶ (Sh(B), O_B) of ringed topoi, an O-module G, and a
map c : f⁻¹J ⟶ G of sheaves of f⁻¹O_B-modules, a solution of the diagram
0 ⟶ G ⟶ ? ⟶ O ⟶ 0 over 0 ⟶ f⁻¹J ⟶ f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ 0
is a first-order thickening i of (Sh(C), O) with Ker(i♯) identified with G
together with a morphism of thickenings (f, f') such that (f')♯ induces c. -/
@[stacks 08V4] #check (RingedSite.FirstOrderThickening.Solution :
  (t : OB' ⟶ OB) → [IsFirstOrderThickening t] →
    (f : RingedSite.ToposHom (RingedSite.ofCommRingSheaf JC O)
      (RingedSite.ofCommRingSheaf JD OB)) →
    (G : SheafOfModules.{max u v} (ringSheaf JC O)) →
    (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G) →
    Type (max u v + 1))

end
