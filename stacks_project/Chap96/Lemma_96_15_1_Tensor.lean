/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FppfTensor
public import stacks_project.Chap96.Definition_96_11_1_QCoh

/-! # Compatibility names for the direct fppf tensor presentation -/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
  SheafOfModules SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The commutative structure sheaf on the fppf site. -/
abbrev commFppfStructureSheaf (X : GroupoidsOver S) :
    Sheaf (inheritedFppfTopology X) CommRingCat.{u} :=
  commAssociatedStructureSheaf X .fppf

/-- Modules over the commutative structure sheaf on the fppf site. -/
abbrev commFppfModules (X : GroupoidsOver S) : Type (u + 1) :=
  commAssociatedModules X .fppf

/-- The sheafification of the pointwise tensor of fppf modules. -/
abbrev commFppfModuleTensor {X : GroupoidsOver S} (F G : commFppfModules X) :
    commFppfModules X := associatedModuleTensor F G

/-- The sheafified tensor agrees with the ringed-site tensor. -/
abbrev commFppfModuleTensorIso {X : GroupoidsOver S} (F G : commFppfModules X) :
    commFppfModuleTensor F G ≅
      moduleTensorAssociated F G :=
  associatedModuleTensorIso F G

namespace QCoh

variable {X : GroupoidsOver S}

/-- The ambient tensor in direct commutative fppf coefficients. -/
abbrev moduleTensor [AlgebraicStack X] (F G : QCoh X) : commFppfModules X :=
  Fppf.moduleTensor F G

/-- The quasi-coherent tensor with its underlying ambient fppf module. -/
abbrev tensor [AlgebraicStack X] (F G : QCoh X) : QCoh X := Fppf.tensor F G

/-- The canonical direct fppf tensor comparison. -/
abbrev tensorComparison [AlgebraicStack X] (F G : QCoh X) :
    moduleTensor F G ⟶ (toCommFppfModules X).obj (tensor F G).obj :=
  Fppf.tensorComparison F G

/-- The pure-tensor pairing on universe-lifted fppf modules. -/
abbrev moduleTensorLiftBilinear [AlgebraicStack X] (M N : commFppfModules X) :
    SheafOfModules.RingedSite.SectionBilinearMap.{u + 1, u}
      (commAssociatedStructureSheafLift X .fppf)
      ((commAssociatedModulesLiftFunctor X .fppf).obj M)
      ((commAssociatedModulesLiftFunctor X .fppf).obj N)
      ((commAssociatedModulesLiftFunctor X .fppf).obj
        (moduleTensorAssociated M N)) :=
  Fppf.moduleTensorLiftBilinear M N

end QCoh

end AlgebraicGeometry.GroupoidsOver
