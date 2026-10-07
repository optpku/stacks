module

public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import stacks_project.Chap85.Definition_85_13_1_System

/-!
# Derived abelian systems extracted from objects of D(C_total)

An object `K` of `D(C_total)` determines the simplicial system `(K_n, K(φ))`
with `K_n` the restriction to `D(C_n)` and `K(φ) : f_φ⁻¹ K_m ⟶ K_n` the canonical
derived comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

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

/-- The identity operator acts on the system extracted from `K` by the canonical
comparison `id ⟶ f_id⁻¹`. -/
theorem toDerivedSystem_map_id
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) (n : SimplexCategory) :
    (derivedInverseImageIdComparisonOf (fun n ↦ (J n).toGrothendieck)
          (fun φ ↦ abelianInverseImage C J φ)
          ((instHasAbelianInverseImageFunctoriality_abelianInverseImage C J).pullbackIdIso n)).app
        ((derivedComponent C J n).obj K) ≫
      derivedTransition C J (𝟙 n) K =
      𝟙 ((derivedComponent C J n).obj K) :=
  sorry

/-- Transitions of the system extracted from `K` respect composition of simplex operators
after the canonical comparison `f_φ⁻¹ ∘ f_ψ⁻¹ ⟶ f_{ψ ≫ φ}⁻¹`. -/
theorem toDerivedSystem_map_comp
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (derivedInverseImageCompComparisonOf (fun n ↦ (J n).toGrothendieck)
          (fun φ ↦ abelianInverseImage C J φ) ψ φ
          ((instHasAbelianInverseImageFunctoriality_abelianInverseImage C J).pullbackCompIso
            ψ φ)).app
        ((derivedComponent C J l).obj K) ≫
      derivedTransition C J (ψ ≫ φ) K =
      (abelianInverseImage C J φ).mapDerivedCategory.map (derivedTransition C J ψ K) ≫
        derivedTransition C J φ K :=
  sorry

/-- The simplicial system `(K_n, K(φ))` of the derived category attached to an object `K`
of `D(C_total)`, with `K_n` the restriction of `K` to `D(C_n)` and
`K(φ) : f_φ⁻¹ K_m ⟶ K_n`. -/
def toDerivedSystem (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    DerivedAbelianSystemOnComponents C J :=
  DerivedAbelianSystem.of (fun n ↦ (derivedComponent C J n).obj K)
    (fun φ ↦ derivedTransition C J φ K)
    (toDerivedSystem_map_id C J K) (toDerivedSystem_map_comp C J K)

/-- The stage object of `toDerivedSystem K` at `n` is the restriction `K_n`. -/
theorem toDerivedSystem_obj
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) (n : SimplexCategory) :
    (toDerivedSystem C J K).obj n = (derivedComponent C J n).obj K :=
  sorry

/-- The transition of `toDerivedSystem K` at `φ` is the canonical comparison
`K(φ) : f_φ⁻¹ K_m ⟶ K_n`. -/
theorem toDerivedSystem_map
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (toDerivedSystem C J K).map φ = derivedTransition C J φ K :=
  sorry

/-- If `K` is cartesian in `D(C_total)`, then the extracted system `(K_n, K(φ))` is cartesian. -/
instance toDerivedSystem_isCartesian
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [Derived.IsCartesian C J K] :
    DerivedAbelianSystem.IsCartesian (toDerivedSystem C J K) where
  isIso_map := sorry

end CategoryTheory.SimplicialSites
