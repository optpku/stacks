/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u v w

/- Definition 27.6.1: the vector bundle associated to `ℱ` is the relative spectrum over `S` of
the symmetric algebra of `ℱ`. -/
@[stacks 01M2] #check (AlgebraicGeometry.Scheme.associatedVectorBundle :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (ℱ : S.Modules) [ℱ.IsQuasicoherent]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.SymmetricAlgebra.qcAlgebra ℱ))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.Scheme.associatedVectorBundleπ :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (ℱ : S.Modules) [ℱ.IsQuasicoherent]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.SymmetricAlgebra.qcAlgebra ℱ))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      AlgebraicGeometry.Scheme.associatedVectorBundle ℱ P ⟶ S)

#check (SheafOfModules.RingedSite.SymmetricAlgebra.isQuasicoherent :
    ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
      [HasWeakSheafify J AddCommGrpCat.{max u v}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
      {𝒪 : Sheaf J CommRingCat.{max u v}}
      [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
      [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
      (F : SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪) [F.IsQuasicoherent],
      (SheafOfModules.RingedSite.SymmetricAlgebra.sheaf 𝒪 F).IsQuasicoherent)

#check (SheafOfModules.RingedSite.SymmetricAlgebra.isLocallyFree :
    ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
      [HasWeakSheafify J AddCommGrpCat.{max u v}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
      {𝒪 : Sheaf J CommRingCat.{max u v}}
      [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
      [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
      (F : SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪) [F.IsLocallyFree],
      (SheafOfModules.RingedSite.SymmetricAlgebra.sheaf 𝒪 F).IsLocallyFree)
