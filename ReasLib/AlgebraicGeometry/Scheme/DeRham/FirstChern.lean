/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ClassRepresentative
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ChernClass
public import Mathlib.Algebra.Homology.Embedding.Extend

@[expose] public section

open CategoryTheory ComplexShape
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}} (f : X ⟶ S)

namespace FirstChern

/-- Closed logarithmic one-forms map to the additive de Rham object with a degree-one shift. -/
noncomputable def logarithmicInclusion :
    ShiftedHom
      ((DerivedCategory.singleFunctor
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) 0).obj
          (logarithmicForms f 1 : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
      (ClassRepresentative.additiveObject f) (1 : ℤ) :=
  let A := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let L : A := logarithmicForms f 1
  let e := HomologicalComplex.extendSingleIso embeddingUpNat L (1 : ℕ) (1 : ℤ) rfl
  let inclusion : (DerivedCategory.singleFunctor A 1).obj L ⟶
      ClassRepresentative.additiveObject f :=
    (DerivedCategory.singleFunctorIsoCompQ A 1).hom.app L ≫
      DerivedCategory.Q.map e.inv ≫
        DerivedCategory.Q.map
          (HomologicalComplex.extendMap (LogarithmicForms.toDeRham f 1) embeddingUpNat)
  ((DerivedCategory.singleFunctors A).shiftIso 1 0 1 rfl).inv.app L ≫
    inclusion⟦(1 : ℤ)⟧'

/-- Logarithmic first cohomology gives a degree-two additive de Rham representative. -/
noncomputable def logarithmicRepresentative (ξ : LogarithmicForms.H f 1 1) :
    ShiftedHom (ClassRepresentative.integerObject X)
      (ClassRepresentative.additiveObject f) (2 : ℤ) :=
  (Abelian.Ext.hom ξ).comp (logarithmicInclusion f) (by decide)

end FirstChern

/-- The relative de Rham first Chern class is the class of the logarithmic Picard representative. -/
noncomputable def firstChernClass (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    cohomology f 2 :=
  ClassRepresentative.inverse f 2
    (FirstChern.logarithmicRepresentative f (LogarithmicForms.firstChernClass f ℒ))

/-- The additive representative of the de Rham Chern class is its logarithmic representative. -/
theorem firstChernClass_spec (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    ClassRepresentative.map f 2 (firstChernClass f ℒ) =
      FirstChern.logarithmicRepresentative f (LogarithmicForms.firstChernClass f ℒ) := sorry

/-- A relative de Rham class is the first Chern class exactly when its representative is logarithmic. -/
theorem firstChernClass_eq_iff (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (ξ : cohomology f 2) :
    ξ = firstChernClass f ℒ ↔ ClassRepresentative.map f 2 ξ =
      FirstChern.logarithmicRepresentative f (LogarithmicForms.firstChernClass f ℒ) := sorry

end AlgebraicGeometry.Scheme.DeRham
