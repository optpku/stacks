/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Functor.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Naturality
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of the bounded-below cochain functor

Natural transformations and natural isomorphisms of zero-morphism-preserving functors
act termwise on bounded-below cochain complexes.  The API records both functoriality and
the comparison with the ambient category of cochain complexes.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Cochain.Plus

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  {F G H : C ⥤ D}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [H.PreservesZeroMorphisms]

/-- A natural transformation of zero-morphism-preserving functors acts on
bounded-below cochain complexes. -/
@[stacks 014X "bounded-below cochain natural transformation"]
def natTrans (α : F ⟶ G) :
    F.mapCochainComplexPlus ⟶ G.mapCochainComplexPlus :=
  (CochainComplex.plus D).liftNatTrans
    (fun K => (F.mapCochainComplexPlus.obj K).property)
    (fun K => (G.mapCochainComplexPlus.obj K).property)
    (Functor.whiskerLeft (CochainComplex.Plus.ι C)
      (NatTrans.mapHomologicalComplex α (up ℤ)))

/-- The underlying component of the induced bounded-below transformation is the
termwise ambient component. -/
@[simp]
theorem natTrans_app_hom (α : F ⟶ G) (K : CochainComplex.Plus C) :
    ((natTrans α).app K).hom =
      (NatTrans.mapHomologicalComplex α (up ℤ)).app K.obj := sorry

/-- Forgetting bounded-below structure recovers the termwise ambient natural
transformation after the source inclusion. -/
theorem whiskerRight_natTrans (α : F ⟶ G) :
    Functor.whiskerRight (natTrans α) (CochainComplex.Plus.ι D) =
      Functor.whiskerLeft (CochainComplex.Plus.ι C)
        (NatTrans.mapHomologicalComplex α (up ℤ)) := sorry

/-- The bounded-below cochain action preserves identity natural transformations. -/
@[simp]
theorem natTrans_id : natTrans (𝟙 F) = 𝟙 F.mapCochainComplexPlus := sorry

/-- The bounded-below cochain action preserves vertical composition. -/
@[simp]
theorem natTrans_comp (α : F ⟶ G) (β : G ⟶ H) :
    natTrans (α ≫ β) = natTrans α ≫ natTrans β := sorry

/-- A natural isomorphism of zero-morphism-preserving functors acts on bounded-below
cochain complexes. -/
@[stacks 014X "bounded-below cochain natural isomorphism"]
def natIso (e : F ≅ G) :
    F.mapCochainComplexPlus ≅ G.mapCochainComplexPlus :=
  (CochainComplex.plus D).liftNatIso
    (fun K => (F.mapCochainComplexPlus.obj K).property)
    (fun K => (G.mapCochainComplexPlus.obj K).property)
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι C)
      (NatIso.mapHomologicalComplex e (up ℤ)))

/-- The forward map of the induced bounded-below natural isomorphism is the induced
natural transformation. -/
@[simp]
theorem natIso_hom (e : F ≅ G) : (natIso e).hom = natTrans e.hom := sorry

/-- The inverse map of the induced bounded-below natural isomorphism is the induced
natural transformation in the reverse direction. -/
@[simp]
theorem natIso_inv (e : F ≅ G) : (natIso e).inv = natTrans e.inv := sorry

/-- The underlying forward component of the induced bounded-below natural isomorphism
is the ambient termwise component. -/
@[simp]
theorem natIso_hom_app_hom (e : F ≅ G) (K : CochainComplex.Plus C) :
    ((natIso e).hom.app K).hom =
      (NatIso.mapHomologicalComplex e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the induced bounded-below natural isomorphism
is the ambient termwise component. -/
@[simp]
theorem natIso_inv_app_hom (e : F ≅ G) (K : CochainComplex.Plus C) :
    ((natIso e).inv.app K).hom =
      (NatIso.mapHomologicalComplex e (up ℤ)).inv.app K.obj := sorry

end CategoryTheory.Functor.Cochain.Plus
