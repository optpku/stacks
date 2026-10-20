module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Mapping-cone and mapping-cocone factorizations from a null-homotopy

The two canonical factorization maps are exposed as concrete data, with separate specification
lemmas.  This keeps downstream code independent of the implementation details of `desc` and
`lift` while retaining the textbook existential bridges.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

universe v u

namespace CochainComplex

open HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L M : CochainComplex C ℤ}

/-- The cocycle equation needed to descend the mapping-cone factorization map. -/
theorem MappingConeFactorization.condition
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    δ (-1) 0 (Cochain.ofHomotopy H) = Cochain.ofHom (f ≫ g) := sorry

/-- The canonical map from `mappingCone f` to `M` induced by a null-homotopy of `f ≫ g`. -/
@[stacks 08RI "mapping-cone factorization map"]
noncomputable def MappingConeFactorization.map
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    mappingCone f ⟶ M :=
  mappingCone.desc f (Cochain.ofHomotopy H) g
    (MappingConeFactorization.condition f g H)

/-- The factorization map restricts to `g` on the cone inclusion of `L`. -/
@[simp, stacks 08RI "mapping-cone factorization computation"]
theorem MappingConeFactorization.inr_comp
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    mappingCone.inr f ≫ MappingConeFactorization.map f g H = g := sorry

/-- The cocycle equation needed to descend the mapping-cocone factorization map. -/
theorem MappingCoconeFactorization.condition
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    δ (-1) 0 (Cochain.ofHomotopy H.symm) + Cochain.ofHom (f ≫ g) = 0 := sorry

/-- The canonical map from `K` to `mappingCocone g` induced by a null-homotopy of `f ≫ g`. -/
@[stacks 08RI "mapping-cocone factorization map"]
noncomputable def MappingCoconeFactorization.map
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    K ⟶ mappingCocone g :=
  mappingCocone.lift g f (Cochain.ofHomotopy H.symm)
    (MappingCoconeFactorization.condition f g H)

/-- The factorization map restricts to `f` on the cocone projection of `L`. -/
@[simp, stacks 08RI "mapping-cocone factorization computation"]
theorem MappingCoconeFactorization.comp_fst
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    MappingCoconeFactorization.map f g H ≫ mappingCocone.fst g = f := sorry

/-- Lemma 13.9.3 (1): a null-homotopic composite factors through its mapping cone. -/
@[stacks 08RI "mapping-cone null-homotopy factorization"]
theorem MappingConeFactorization.exists
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    ∃ γ : mappingCone f ⟶ M, mappingCone.inr f ≫ γ = g := sorry

/-- Lemma 13.9.3 (2): a null-homotopic composite factors through its shifted mapping cocone. -/
@[stacks 08RI "mapping-cocone null-homotopy factorization"]
theorem MappingCoconeFactorization.exists
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    ∃ γ : K ⟶ mappingCocone g, γ ≫ mappingCocone.fst g = f := sorry

end CochainComplex
