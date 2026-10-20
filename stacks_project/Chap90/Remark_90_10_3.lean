module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Types

/-!
# Schlessinger's conditions (H1) and (H2)

When a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is cofibered in sets,
the categorical conditions (S1) and (S2) are equivalent to Schlessinger's (H1) and (H2).
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

variable {F : ArtinianLocalAlgCat Λ k ⥤ Type v}

/- Remark 90.10.3 (1) -/
@[stacks 06HY] #check
  (CategoryTheory.Functor.hasSchlessingerS1_iff_hasSchlessingerH1 (Λ := Λ) (k := k) F :
    CategoryTheory.Functor.HasSchlessingerS1 (CategoryTheory.CategoryOfElements.π F) ↔
      CategoryTheory.Functor.HasSchlessingerH1 F)

/- Remark 90.10.3 (2) -/
@[stacks 06HY] #check
  (CategoryTheory.Functor.hasSchlessingerS2_iff_hasSchlessingerH2 (Λ := Λ) (k := k) F :
    CategoryTheory.Functor.HasSchlessingerS2 (CategoryTheory.CategoryOfElements.π F) ↔
      CategoryTheory.Functor.HasSchlessingerH2 F)

/- Remark 90.10.3 (3) -/
@[stacks 06HY] #check
  (CategoryTheory.Functor.pullbackObjMap_subtype_injective_iff_unique
    (Λ := Λ) (k := k) F :
    ∀ {A P : ArtinianLocalAlgCat Λ k} (f : A ⟶ residue Λ k)
      (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
      (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)),
      Function.Injective
          (CategoryTheory.Functor.pullbackObjMap_subtype F π1 π2 f
            (dualNumberToResidue Λ k) h) ↔
        ∀ y₁ y₂ : F.obj P,
          F.map π1 y₁ = F.map π1 y₂ →
            F.map π2 y₁ = F.map π2 y₂ → y₁ = y₂)

end CategoryTheory.Functor
