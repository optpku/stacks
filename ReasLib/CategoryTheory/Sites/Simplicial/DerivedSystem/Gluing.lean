/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- A compatible family between restriction systems lifts to a total morphism when the
source is cartesian and the degreewise shifted Hom groups vanish above degree one. -/
theorem exists_hom_of_toDerivedSystemHom
    (K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [AbelianDerived.IsCartesian C J K]
    (h_hom : ∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((toDerivedSystem C J K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶ (toDerivedSystem C J K').obj n))
    (α : DerivedSystem.Hom (toDerivedSystem C J K) (toDerivedSystem C J K')) :
    ∃ f : K ⟶ K', ∀ n, (toDerivedSystemMap C J f).app n = α.app n :=
  sorry

/-- A cartesian derived system with vanishing positive shifted self-Hom groups is realized
by a cartesian total derived object with an invertible compatible family of components. -/
theorem exists_isCartesian_of_derivedSystem
    (Ksys : DerivedSystem (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact C J φ).obj)
      (AbelianDerived.inverseImageCompIso C J))
    (h_cartesian : DerivedSystem.IsCartesian Ksys)
    (h_hom : ∀ (n : SimplexCategory) (t : ℤ), 0 < t →
      Subsingleton ((Ksys.obj n)⟦t⟧ ⟶ Ksys.obj n)) :
    ∃ (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
      (α : DerivedSystem.Hom (toDerivedSystem C J K) Ksys),
      AbelianDerived.IsCartesian C J K ∧ ∀ n, IsIso (α.app n) :=
  sorry

end CategoryTheory.SimplicialSites
