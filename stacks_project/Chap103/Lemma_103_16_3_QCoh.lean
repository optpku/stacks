/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap103.Lemma_103_16_2

/-!
# Quasi-coherent modules on the étale, lisse-étale, and flat-fppf sites

The category `QCoh(𝒪_X)` of an algebraic stack may be read on the associated
étale site, and likewise after restriction to the lisse-étale and flat-fppf
sites. These are the full subcategories of `SheafOfModules.IsQuasicoherent`
on the corresponding module categories.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The object property of quasi-coherent étale `𝒪_X`-modules. -/
abbrev etaleQuasiCoherent (X : GroupoidsOver S) :
    ObjectProperty (etaleModules X) :=
  SheafOfModules.isQuasicoherent (etaleStructureSheaf X)

/-- An étale `𝒪_X`-module lies in `etaleQuasiCoherent` if and only if it is
quasi-coherent. -/
theorem mem_etaleQCoh_iff {X : GroupoidsOver S} (F : etaleModules X) :
    etaleQuasiCoherent X F ↔ F.IsQuasicoherent :=
  sorry

/-- The category of quasi-coherent modules on the associated étale site of `X`.
By Sheaves on Stacks, Lemma 96.11.4 this is the lisse-étale reading of
`QCoh(𝒪_X)`. -/
abbrev etaleQCoh (X : GroupoidsOver S) :=
  (etaleQuasiCoherent X).FullSubcategory

namespace etaleQCoh

/-- The inclusion of quasi-coherent étale modules into all étale `𝒪_X`-modules. -/
abbrev inclusion (X : GroupoidsOver S) :
    etaleQCoh X ⥤ etaleModules X :=
  (etaleQuasiCoherent X).ι

end etaleQCoh

/-- The object property of quasi-coherent modules on the lisse-étale site of an
algebraic stack. -/
abbrev lisseEtaleQuasiCoherent (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :=
  SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X)

/-- A lisse-étale `𝒪`-module lies in `lisseEtaleQuasiCoherent` if and only if it
is quasi-coherent. -/
theorem mem_lisseEtaleQCoh_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :
    lisseEtaleQuasiCoherent X H ↔ H.IsQuasicoherent :=
  sorry

/-- The category of quasi-coherent modules on the lisse-étale site of an
algebraic stack. -/
abbrev lisseEtaleQCoh (X : GroupoidsOver S) [AlgebraicStack X] :=
  (lisseEtaleQuasiCoherent X).FullSubcategory

namespace lisseEtaleQCoh

/-- The inclusion of quasi-coherent lisse-étale modules into all lisse-étale
`𝒪`-modules. -/
abbrev inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleQCoh X ⥤ SheafOfModules.{u} (lisseEtaleStructureSheaf X) :=
  (lisseEtaleQuasiCoherent X).ι

end lisseEtaleQCoh

/-- The object property of quasi-coherent modules on the flat-fppf site of an
algebraic stack. -/
abbrev flatFppfQuasiCoherent (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (SheafOfModules.{u} (flatFppfStructureSheaf X)) :=
  SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X)

/-- A flat-fppf `𝒪`-module lies in `flatFppfQuasiCoherent` if and only if it is
quasi-coherent. -/
theorem mem_flatFppfQCoh_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X)) :
    flatFppfQuasiCoherent X H ↔ H.IsQuasicoherent :=
  sorry

/-- The category of quasi-coherent modules on the flat-fppf site of an
algebraic stack. -/
abbrev flatFppfQCoh (X : GroupoidsOver S) [AlgebraicStack X] :=
  (flatFppfQuasiCoherent X).FullSubcategory

namespace flatFppfQCoh

/-- The inclusion of quasi-coherent flat-fppf modules into all flat-fppf
`𝒪`-modules. -/
abbrev inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfQCoh X ⥤ SheafOfModules.{u} (flatFppfStructureSheaf X) :=
  (flatFppfQuasiCoherent X).ι

end flatFppfQCoh

end AlgebraicGeometry.AlgebraicStack
