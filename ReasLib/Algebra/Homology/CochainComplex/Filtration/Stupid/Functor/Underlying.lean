/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid.Functor
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The underlying functor of the stupid filtration

Forgetting the filtration on the canonical stupid filtration recovers the
original cochain complex.  This leaf packages that objectwise fact as a
functor-level natural isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Stupid

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The composite functor which equips a cochain complex with its stupid filtration and then
forgets that filtration. -/
@[stacks 0D8Z "underlying functor of the stupid filtration"]
abbrev underlyingFunctor :
    CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  functor (A := A) ⋙ FilteredComplex.underlyingFunctor

/-- The object part of the stupid-filtration underlying functor is the original complex. -/
@[simp, stacks 0D8Z "object computation for the stupid-filtration underlying functor"]
theorem underlyingFunctor_obj (K : CochainComplex A ℤ) :
    (underlyingFunctor (A := A)).obj K = K := sorry

/-- The map part of the stupid-filtration underlying functor is the original cochain map. -/
@[simp, stacks 0D8Z "map computation for the stupid-filtration underlying functor"]
theorem underlyingFunctor_map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (underlyingFunctor (A := A)).map f = f := sorry

/-- The canonical objectwise comparison from the underlying stupid filtration to the source
complex. -/
@[stacks 0D8Z "objectwise comparison for the stupid-filtration underlying functor"]
noncomputable def underlyingIso (K : CochainComplex A ℤ) :
    (underlyingFunctor (A := A)).obj K ≅ K :=
  Iso.refl K

namespace underlyingIso

/-- The forward map of the objectwise stupid-filtration comparison is the identity map. -/
@[simp, stacks 0D8Z "forward objectwise stupid-filtration comparison"]
theorem hom (K : CochainComplex A ℤ) :
    (underlyingIso K).hom = 𝟙 K := sorry

/-- The inverse map of the objectwise stupid-filtration comparison is the identity map. -/
@[simp, stacks 0D8Z "inverse objectwise stupid-filtration comparison"]
theorem inv (K : CochainComplex A ℤ) :
    (underlyingIso K).inv = 𝟙 K := sorry

/-- The stupid-filtration underlying comparison is natural in cochain-complex maps. -/
@[reassoc, stacks 0D8Z "naturality of the stupid-filtration underlying comparison"]
theorem hom_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (underlyingFunctor (A := A)).map f ≫ (underlyingIso L).hom =
      (underlyingIso K).hom ≫ f := sorry

end underlyingIso

/-- The stupid-filtration underlying functor is naturally isomorphic to the identity functor. -/
@[stacks 0D8Z "functor-level stupid-filtration underlying comparison"]
noncomputable def underlyingNatIso :
    underlyingFunctor (A := A) ≅ 𝟭 (CochainComplex A ℤ) :=
  NatIso.ofComponents (fun K ↦ underlyingIso K)
    (fun {_ _} f ↦ underlyingIso.hom_naturality f)

namespace underlyingNatIso

/-- The forward stupid-filtration underlying comparison satisfies its naturality square. -/
@[reassoc, stacks 0D8Z "forward naturality of the stupid-filtration underlying comparison"]
theorem hom_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (underlyingFunctor (A := A)).map f ≫
        (underlyingNatIso (A := A)).hom.app L =
      (underlyingNatIso (A := A)).hom.app K ≫ f := sorry

/-- The inverse stupid-filtration underlying comparison satisfies the reverse naturality square.
-/
@[reassoc, stacks 0D8Z "inverse naturality of the stupid-filtration underlying comparison"]
theorem inv_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    f ≫ (underlyingNatIso (A := A)).inv.app L =
      (underlyingNatIso (A := A)).inv.app K ≫
        (underlyingFunctor (A := A)).map f := sorry

/-- A component of `underlyingNatIso` is the canonical objectwise comparison. -/
@[simp, stacks 0D8Z "component of the stupid-filtration underlying natural isomorphism"]
theorem app (K : CochainComplex A ℤ) :
    (underlyingNatIso (A := A)).app K = underlyingIso K := sorry

/-- The forward component of `underlyingNatIso` is the canonical identity comparison. -/
@[simp, stacks 0D8Z "forward component of the stupid-filtration underlying natural isomorphism"]
theorem hom_app (K : CochainComplex A ℤ) :
    (underlyingNatIso (A := A)).hom.app K = (underlyingIso K).hom := sorry

/-- The inverse component of `underlyingNatIso` is the canonical identity comparison. -/
@[simp, stacks 0D8Z "inverse component of the stupid-filtration underlying natural isomorphism"]
theorem inv_app (K : CochainComplex A ℤ) :
    (underlyingNatIso (A := A)).inv.app K = (underlyingIso K).inv := sorry

end underlyingNatIso

end CategoryTheory.CochainComplex.Stupid

end
