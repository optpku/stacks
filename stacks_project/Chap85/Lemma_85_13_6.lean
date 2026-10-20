module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_13_2_System

/-!
# Lemma 85.13.6

In Situation 85.3.3, a morphism of associated simplicial systems of objects
`K, K'` of `D(C_total)` is induced by a morphism `K ⟶ K'` when `K` is cartesian
and `Hom(K_i⟦i - 1⟧, K'_i) = 0` for `i > 1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- The morphism of associated simplicial systems induced by a morphism in `D(C_total)`. -/
def toDerivedSystemMap
    {K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})} (f : K ⟶ K') :
    DerivedAbelianSystem.Hom (toDerivedSystem C J K) (toDerivedSystem C J K') :=
  DerivedAbelianSystem.homMk (fun n ↦ (derivedComponent C J n).map f) sorry

/-- The stage-`n` component of `toDerivedSystemMap f` is the restriction of `f`. -/
theorem toDerivedSystemMap_app
    {K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})}
    (f : K ⟶ K') (n : SimplexCategory) :
    (toDerivedSystemMap C J f).app n = (derivedComponent C J n).map f :=
  sorry

/-- Lemma 85.13.6
In Situation 85.3.3, if `K, K'` are objects of `D(C_total)`, `K` is cartesian, and
`Hom(K_i⟦i - 1⟧, K'_i) = 0` for `i > 1`, then every morphism of associated simplicial
systems `{K_n ⟶ K'_n}` comes from a morphism `K ⟶ K'` in `D(C_total)`. -/
@[stacks 0D9K]
theorem exists_hom_of_toDerivedSystemHom
    (K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [Derived.IsCartesian C J K]
    (h_hom : ∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((toDerivedSystem C J K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶ (toDerivedSystem C J K').obj n))
    (α : DerivedAbelianSystem.Hom (toDerivedSystem C J K) (toDerivedSystem C J K')) :
    ∃ f : K ⟶ K', ∀ n, (toDerivedSystemMap C J f).app n = α.app n :=
  sorry

end CategoryTheory.SimplicialSites
