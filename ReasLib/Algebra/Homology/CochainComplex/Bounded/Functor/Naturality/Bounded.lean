/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Functor.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Naturality
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of the bounded cochain functor

Natural transformations and natural isomorphisms of zero-morphism-preserving functors
restrict to bounded cochain complexes.  Their underlying components remain the ambient
termwise components.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Cochain.Bounded

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  {F G H : C ⥤ D}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [H.PreservesZeroMorphisms]

/-- A natural transformation of zero-morphism-preserving functors restricts to bounded
cochain complexes. -/
@[stacks 014X "bounded cochain natural transformation"]
def natTrans (α : F ⟶ G) : map F ⟶ map G :=
  ObjectProperty.FullSubcategory.restrict.natTrans
    (mapsTo F) (mapsTo G) (NatTrans.mapHomologicalComplex α (up ℤ))

/-- The underlying component of the induced bounded transformation is the termwise
ambient component. -/
@[simp]
theorem natTrans_app_hom (α : F ⟶ G) (K : CochainComplex.Bounded C) :
    ((natTrans α).app K).hom =
      (NatTrans.mapHomologicalComplex α (up ℤ)).app K.obj := sorry

/-- Forgetting bounded structure recovers the termwise ambient natural transformation
after the source inclusion. -/
theorem whiskerRight_natTrans (α : F ⟶ G) :
    Functor.whiskerRight (natTrans α) (CochainComplex.Bounded.ι D) =
      Functor.whiskerLeft (CochainComplex.Bounded.ι C)
        (NatTrans.mapHomologicalComplex α (up ℤ)) := sorry

/-- The bounded cochain action preserves identity natural transformations. -/
@[simp]
theorem natTrans_id : natTrans (𝟙 F) = 𝟙 (map F) := sorry

/-- The bounded cochain action preserves vertical composition. -/
@[simp]
theorem natTrans_comp (α : F ⟶ G) (β : G ⟶ H) :
    natTrans (α ≫ β) = natTrans α ≫ natTrans β := sorry

/-- A natural isomorphism of zero-morphism-preserving functors restricts to bounded
cochain complexes. -/
@[stacks 014X "bounded cochain natural isomorphism"]
def natIso (e : F ≅ G) : map F ≅ map G :=
  ObjectProperty.FullSubcategory.restrict.natIso
    (mapsTo F) (mapsTo G) (NatIso.mapHomologicalComplex e (up ℤ))

/-- The forward map of the induced bounded natural isomorphism is the induced natural
transformation. -/
@[simp]
theorem natIso_hom (e : F ≅ G) : (natIso e).hom = natTrans e.hom := sorry

/-- The inverse map of the induced bounded natural isomorphism is the induced natural
transformation in the reverse direction. -/
@[simp]
theorem natIso_inv (e : F ≅ G) : (natIso e).inv = natTrans e.inv := sorry

/-- The underlying forward component of the induced bounded natural isomorphism is the
ambient termwise component. -/
@[simp]
theorem natIso_hom_app_hom (e : F ≅ G) (K : CochainComplex.Bounded C) :
    ((natIso e).hom.app K).hom =
      (NatIso.mapHomologicalComplex e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the induced bounded natural isomorphism is the
ambient termwise component. -/
@[simp]
theorem natIso_inv_app_hom (e : F ≅ G) (K : CochainComplex.Bounded C) :
    ((natIso e).inv.app K).hom =
      (NatIso.mapHomologicalComplex e (up ℤ)).inv.app K.obj := sorry

end CategoryTheory.Functor.Cochain.Bounded
