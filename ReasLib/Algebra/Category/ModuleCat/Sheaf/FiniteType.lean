/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.ObjectProperty.Representatives
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-Type Sheaves of Modules

This file owns closure properties of Mathlib's
`SheafOfModules.IsFiniteType` predicate.  The statements live over an
arbitrary sheaf of rings on a site; ringed-space formulations are obtained by
specialization.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v u'

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

section Free

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A free module sheaf on a finite indexing type
is of finite type. -/
@[stacks 01BP "finite free module sheaves"]
instance free_isFiniteType (I : Type u) [Finite I] :
    (free (R := R) I).IsFiniteType := sorry

end Free

section Isomorphisms

variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The object property of finite-type `R`-module sheaves is invariant under isomorphism. -/
instance isFiniteType_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFiniteType : ObjectProperty (SheafOfModules.{u} R)) := sorry

/-- Transporting a finite-type `R`-module sheaf across an isomorphism preserves finite type. -/
theorem isFiniteType_of_iso
    {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] :
    N.IsFiniteType := sorry

end Isomorphisms

section Quotients

variable [HasSheafify J AddCommGrpCat.{u}]
  [HasSheafify J (Type u)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- A quotient of a finite-type sheaf of `R`-modules is finite type. -/
theorem isFiniteType_of_epi
    {M N : SheafOfModules.{u} R} (p : M ⟶ N) [Epi p] [M.IsFiniteType] :
    N.IsFiniteType := sorry

/-- The finite-type module-sheaf property is closed under quotients. -/
instance isFiniteType_isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (IsFiniteType : ObjectProperty (SheafOfModules.{u} R)) := sorry

/-- The cokernel of a map into a finite-type sheaf of `R`-modules is finite type. -/
theorem isFiniteType_cokernel
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) [N.IsFiniteType] :
    (cokernel f).IsFiniteType := sorry

/-- The coimage of a map from a finite-type sheaf of `R`-modules is finite type. -/
theorem isFiniteType_coimage
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) [M.IsFiniteType] :
    (Abelian.coimage f).IsFiniteType := sorry

/-- The image of a map from a finite-type sheaf of `R`-modules is
finite type. -/
@[stacks 01B7 "(1)"]
theorem isFiniteType_image
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) [M.IsFiniteType] :
    (Abelian.image f).IsFiniteType := sorry

end Quotients

section Extensions

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- The finite-type module-sheaf property is closed under short exact extensions. -/
instance isFiniteType_isClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions
      (IsFiniteType : ObjectProperty (SheafOfModules.{u} R)) := sorry

/-- In a short exact complex of `R`-module sheaves, finite type of the
outer terms implies finite type of the middle term. -/
@[stacks 01B7 "(2)"]
theorem isFiniteType_of_shortExact
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    [S.X₁.IsFiniteType] [S.X₃.IsFiniteType] :
    S.X₂.IsFiniteType := sorry

end Extensions

section Representatives

variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Finite-type module sheaves admit representatives in the maximum of the coefficient,
site-object and site-morphism universes, without the successor needed for the ambient
module-sheaf category. In particular, when all three universes are `u`, the bound is `u`.
The site universes remain in the bound for a general, possibly larger site. -/
@[stacks 01BC "essential smallness"]
instance IsFiniteType.essentiallySmall :
    ObjectProperty.EssentiallySmall.{max u v u'}
      (IsFiniteType : ObjectProperty (SheafOfModules.{u} R)) := sorry

end Representatives

end SheafOfModules
