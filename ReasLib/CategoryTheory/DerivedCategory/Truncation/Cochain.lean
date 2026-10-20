/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Transition

@[expose] public section

/-!
# Canonical Derived Truncations of Cochain Complexes

The canonical lower truncation of the derived image of a cochain complex is
canonically isomorphic to the derived image of its concrete lower truncation.
This file owns the forward comparison morphism and its reusable naturality
API.  The comparison is exposed as a morphism with a canonical `IsIso`
instance, so its non-proof data is independent of any selected inverse.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.TruncGE

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]

/-- The canonical comparison from the abstract lower truncation of `Q.obj K`
to the derived image of the concrete lower truncation `K.truncGE a`. -/
@[stacks 070F]
noncomputable def qHom (K : CochainComplex A ℤ) (a : ℤ) :
    (t.truncGE a).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj (K.truncGE a) :=
  t.descTruncGE (DerivedCategory.Q.map (K.πTruncGE a)) a

/-- The canonical comparison is characterized by its composite with the
abstract lower-truncation projection. -/
@[reassoc (attr := simp), stacks 070F]
theorem qHom_fac (K : CochainComplex A ℤ) (a : ℤ) :
    (t.truncGEπ a).app (DerivedCategory.Q.obj K) ≫ qHom K a =
      DerivedCategory.Q.map (K.πTruncGE a) := sorry

/-- The canonical comparison between the two lower-truncation models is an
isomorphism. -/
@[stacks 070F]
instance qHom_isIso (K : CochainComplex A ℤ) (a : ℤ) :
    IsIso (qHom K a) := sorry

/-- The canonical comparison is natural in the cochain complex. -/
@[reassoc, stacks 070F]
theorem qHom_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (a : ℤ) :
    (t.truncGE a).map (DerivedCategory.Q.map f) ≫ qHom L a =
      qHom K a ≫
        DerivedCategory.Q.map (CochainComplex.truncGEMap f a) := sorry

/-- The canonical comparison intertwines abstract and concrete maps between
lower truncations at ordered cutoffs. -/
@[reassoc, stacks 070F]
theorem qHom_mapOfLE (K : CochainComplex A ℤ) {a b : ℤ} (hab : a ≤ b) :
    (t.natTransTruncGEOfLE a b hab).app (DerivedCategory.Q.obj K) ≫
        qHom K b =
      qHom K a ≫
        DerivedCategory.Q.map (CochainComplex.truncGEMapOfLE K hab) := sorry

namespace qHom

/-- A morphism from the abstract lower truncation is the canonical comparison
as soon as it has the prescribed composite with the truncation projection. -/
@[stacks 070F]
theorem eq_of_fac (K : CochainComplex A ℤ) (a : ℤ)
    {f : (t.truncGE a).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj (K.truncGE a)}
    (hf : (t.truncGEπ a).app (DerivedCategory.Q.obj K) ≫ f =
      DerivedCategory.Q.map (K.πTruncGE a)) :
    f = qHom K a := sorry

/-- The inverse canonical comparison carries the concrete truncation map back
to the abstract truncation projection. -/
@[reassoc (attr := simp), stacks 070F]
theorem map_comp_inv (K : CochainComplex A ℤ) (a : ℤ) :
    DerivedCategory.Q.map (K.πTruncGE a) ≫ inv (qHom K a) =
      (t.truncGEπ a).app (DerivedCategory.Q.obj K) := sorry

end qHom

end CategoryTheory.DerivedCategory.TruncGE
