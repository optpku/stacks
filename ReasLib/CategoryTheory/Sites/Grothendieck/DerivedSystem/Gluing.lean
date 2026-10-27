/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.DerivedSystem

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- A cartesian derived system with vanishing positive shifted self-Hom groups is realized
by a cartesian total derived object with an invertible compatible family of components. -/
theorem exists_isCartesian_of_derivedSystem
    (Ksys : SimplicialSites.DerivedSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact F J φ).obj)
      (AbelianDerived.inverseImageCompIso F J))
    (h_cartesian : SimplicialSites.DerivedSystem.IsCartesian Ksys)
    (h_hom : ∀ (n : SimplexCategory) (t : ℤ), 0 < t →
      Subsingleton ((Ksys.obj n)⟦t⟧ ⟶ Ksys.obj n)) :
    ∃ (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
      (α : SimplicialSites.DerivedSystem.Hom (toDerivedSystem F J K) Ksys),
      AbelianDerived.IsCartesian F J K ∧ ∀ n, IsIso (α.app n) := sorry

/-- A compatible family between restriction systems lifts to a total morphism when the
source is cartesian and the degreewise shifted Hom groups vanish above degree one. -/
theorem exists_hom_of_toDerivedSystemHom
    (K K' : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    [AbelianDerived.IsCartesian F J K]
    (h_hom : ∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((toDerivedSystem F J K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶ (toDerivedSystem F J K').obj n))
    (α : SimplicialSites.DerivedSystem.Hom (toDerivedSystem F J K) (toDerivedSystem F J K')) :
    ∃ f : K ⟶ K', ∀ n, (derivedRestrict F J n).map f = α.app n := sorry

end CategoryTheory.Grothendieck
