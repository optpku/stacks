/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasicoherent modules on schemes

Quasicoherent modules form the full subcategory cut out by mathlib's local
`SheafOfModules.IsQuasicoherent` predicate. This file records the closure properties at their
natural level of an arbitrary scheme; affine chapter statements are direct specializations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme

/-- The structure sheaf module of a scheme is quasi-coherent. -/
instance structureSheaf_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := sorry

/-- The canonical object property of quasi-coherent module sheaves on a scheme.

This is the scheme-level owner used by generic object-property constructions.  The
`QCoh` namespace below provides the categorical view of its full subcategory. -/
@[stacks 01BE "scheme quasicoherent module property"]
abbrev quasiCoherentModuleProperty (X : Scheme.{u}) : ObjectProperty X.Modules :=
  SheafOfModules.isQuasicoherent X.ringCatSheaf

/-- The category of quasicoherent modules in Mathlib's `Scheme.Modules` presentation.

Although the objects agree with `RingedSpace.QCoh X.toRingedSpace`, the two ambient module
categories use distinct category instances. Keeping this full subcategory over `X.Modules`
lets the generic full-subcategory limit and colimit API apply definitionally. -/
@[stacks 01BE "scheme quasicoherent module category"]
abbrev QCoh (X : Scheme.{u}) :=
  (quasiCoherentModuleProperty X).FullSubcategory

namespace QCoh

/-- The inclusion of quasicoherent modules into all module sheaves. -/
@[stacks 01BE "scheme quasicoherent module inclusion"]
abbrev inclusion (X : Scheme.{u}) : QCoh X ⥤ X.Modules :=
  (quasiCoherentModuleProperty X).ι

/-- Quasicoherent modules on a scheme form a weak Serre class.  This is the
canonical owner of closure under zero objects, kernels, cokernels, extensions,
retracts, and finite products. -/
@[stacks 01IC "weak Serre class of quasicoherent modules",
  stacks 01IE "extension closure of quasicoherent modules"]
instance isWeakSerreClass (X : Scheme.{u}) :
    (quasiCoherentModuleProperty X).IsWeakSerreClass := sorry

/-- Quasicoherence is preserved by colimits of every fixed shape on every scheme. -/
@[stacks 01ID "scheme-level colimit closure"]
instance closedUnderColimitsOfShape
    (X : Scheme.{u}) {J : Type v} [Category.{w} J] :
    (quasiCoherentModuleProperty X).IsClosedUnderColimitsOfShape J := sorry

end QCoh

namespace Modules

variable {X : Scheme.{u}}

section KernelCokernel

variable {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- The kernel of a morphism of quasicoherent modules is quasicoherent. -/
@[stacks 01IC "kernel"]
instance isQuasicoherent_kernel (f : F ⟶ G) :
    (kernel f).IsQuasicoherent := sorry

/-- The cokernel of a morphism of quasicoherent modules is quasicoherent. -/
@[stacks 01IC "cokernel"]
instance isQuasicoherent_cokernel (f : F ⟶ G) :
    (cokernel f).IsQuasicoherent := sorry

end KernelCokernel

/-- A colimit of a diagram of quasicoherent modules is quasicoherent. -/
@[stacks 01ID "colimit of quasicoherent modules"]
theorem isQuasicoherent_colimit {J : Type v} [Category.{w} J]
    (F : J ⥤ X.Modules) [HasColimit F]
    (hF : ∀ j, (F.obj j).IsQuasicoherent) :
    (colimit F).IsQuasicoherent := sorry

/-- An arbitrary coproduct of quasicoherent modules on a scheme is quasicoherent. -/
@[stacks 01ID "coproduct"]
theorem isQuasicoherent_coproduct {ι : Type v} (F : ι → X.Modules)
    [HasCoproduct F]
    (hF : ∀ i, (F i).IsQuasicoherent) :
    (∐ F).IsQuasicoherent := sorry

end Modules

end AlgebraicGeometry.Scheme
