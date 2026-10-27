/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.ModuleAbelian
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.Sites

/-!
# Weak Serre subcategories of quasi-coherent modules on algebraic stacks

Quasi-coherent modules on the lisse-étale and flat-fppf sites form weak Serre
subcategories of all modules on those sites. In particular, kernels and
cokernels of morphisms between quasi-coherent modules are quasi-coherent.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

namespace lisseEtaleQCoh

/-- Quasi-coherent lisse-étale modules on an algebraic stack form a weak Serre
subcategory of all lisse-étale modules. -/
@[stacks 07B4]
instance isWeakSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleQuasiCoherent X).IsWeakSerreClass :=
  sorry

/-- The kernel of a morphism of quasi-coherent lisse-étale modules is
quasi-coherent. -/
instance isQuasicoherent_kernel {X : GroupoidsOver S} [AlgebraicStack X]
    {F G : SheafOfModules.{u} (lisseEtaleStructureSheaf X)}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (kernel f).IsQuasicoherent :=
  (lisseEtaleQuasiCoherent X).prop_kernel f inferInstance inferInstance

/-- The cokernel of a morphism of quasi-coherent lisse-étale modules is
quasi-coherent. -/
instance isQuasicoherent_cokernel {X : GroupoidsOver S} [AlgebraicStack X]
    {F G : SheafOfModules.{u} (lisseEtaleStructureSheaf X)}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (cokernel f).IsQuasicoherent :=
  (lisseEtaleQuasiCoherent X).prop_cokernel f inferInstance inferInstance

end lisseEtaleQCoh

namespace flatFppfQCoh

/-- Quasi-coherent flat-fppf modules on an algebraic stack form a weak Serre
subcategory of all flat-fppf modules. -/
@[stacks 07B4]
instance isWeakSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfQuasiCoherent X).IsWeakSerreClass :=
  sorry

/-- The kernel of a morphism of quasi-coherent flat-fppf modules is
quasi-coherent. -/
instance isQuasicoherent_kernel {X : GroupoidsOver S} [AlgebraicStack X]
    {F G : SheafOfModules.{u} (flatFppfStructureSheaf X)}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (kernel f).IsQuasicoherent :=
  (flatFppfQuasiCoherent X).prop_kernel f inferInstance inferInstance

/-- The cokernel of a morphism of quasi-coherent flat-fppf modules is
quasi-coherent. -/
instance isQuasicoherent_cokernel {X : GroupoidsOver S} [AlgebraicStack X]
    {F G : SheafOfModules.{u} (flatFppfStructureSheaf X)}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (cokernel f).IsQuasicoherent :=
  (flatFppfQuasiCoherent X).prop_cokernel f inferInstance inferInstance

end flatFppfQCoh

end AlgebraicGeometry.AlgebraicStack
