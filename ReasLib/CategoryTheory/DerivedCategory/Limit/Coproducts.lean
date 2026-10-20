module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproducts in Derived Categories

This module owns the shape-generic coproduct API for derived categories.  Exact coproducts in
the ambient abelian category are preserved by localization, and Grothendieck abelian categories
supply the resulting derived coproducts for every available universe level.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u uJ

namespace CategoryTheory.DerivedCategory.Coproduct

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {J : Type uJ}

/-- Localization to the derived category preserves a coproduct of complexes whenever that
discrete coproduct is exact in the ambient abelian category. -/
@[stacks 0A5L]
instance q_preservesCoproduct_of_exact
    [HasCoproductsOfShape J A] [HasExactColimitsOfShape (Discrete J) A]
    (K : J → CochainComplex A ℤ) :
    PreservesColimit (Discrete.functor K) DerivedCategory.Q := sorry

/-- A termwise coproduct of complexes realizes the coproduct of its images whenever the chosen
derived localization preserves that particular coproduct. Keeping preservation explicit makes
this data constructor independent of how preservation is proved. -/
@[stacks 0A5L, stacks 07D9 "termwise coproduct model"]
noncomputable def cofanIsColimit_of_termwise
    (K : J → CochainComplex A ℤ) [HasCoproduct K]
    [PreservesColimit (Discrete.functor K) DerivedCategory.Q] :
    IsColimit
      (Cofan.mk
        (DerivedCategory.Q.obj (∐ K))
        (fun j ↦ DerivedCategory.Q.map (Sigma.ι K j))) :=
  Limits.isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q K

/-- The discrete diagram of localized representative complexes is isomorphic to the prescribed
derived diagram. -/
@[stacks 0A5L]
noncomputable def modelDiagramIso
    (X : J → DerivedCategory A) (K : J → CochainComplex A ℤ)
    (eK : ∀ j, DerivedCategory.Q.obj (K j) ≅ X j) :
    Discrete.functor (fun j ↦ DerivedCategory.Q.obj (K j)) ≅ Discrete.functor X :=
  Discrete.natIso fun j ↦ eK j.as

/-- The cofan on a derived diagram obtained from a coproduct of chosen representative
complexes. -/
@[stacks 0A5L]
noncomputable def modelCofan
    (X : J → DerivedCategory A) (K : J → CochainComplex A ℤ)
    [HasCoproduct K] (eK : ∀ j, DerivedCategory.Q.obj (K j) ≅ X j) :
    Cofan X :=
  (Cocone.precompose (modelDiagramIso X K eK).inv).obj
    (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun j ↦ DerivedCategory.Q.map (Sigma.ι K j)))

/-- The inclusion of a chosen derived object into its representative-model cofan. -/
@[stacks 0A5L]
theorem modelCofan_inj
    (X : J → DerivedCategory A) (K : J → CochainComplex A ℤ)
    [HasCoproduct K] (eK : ∀ j, DerivedCategory.Q.obj (K j) ≅ X j) (j : J) :
    (modelCofan X K eK).inj j =
      (eK j).inv ≫ DerivedCategory.Q.map (Sigma.ι K j) := sorry

/-- A coproduct of representative complexes realizes the coproduct of their images in the
derived category whenever localization preserves that coproduct. -/
@[stacks 0A5L]
noncomputable def modelCofanIsColimit
    (X : J → DerivedCategory A) (K : J → CochainComplex A ℤ)
    [HasCoproduct K] [PreservesColimit (Discrete.functor K) DerivedCategory.Q]
    (eK : ∀ j, DerivedCategory.Q.obj (K j) ≅ X j) :
    IsColimit (modelCofan X K eK) :=
  (IsColimit.precomposeInvEquiv
    (modelDiagramIso X K eK)
    (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun j ↦ DerivedCategory.Q.map (Sigma.ι K j)))).invFun
    (Limits.isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q K)

/-- Exact coproducts of a prescribed discrete shape in an abelian category induce coproducts of
that shape in its derived category. -/
@[stacks 0A5L]
instance hasCoproductsOfShape_of_exact
    [HasCoproductsOfShape J A] [HasExactColimitsOfShape (Discrete J) A] :
    HasCoproductsOfShape J (DerivedCategory A) := sorry

/-- A Grothendieck abelian category has coproducts of every prescribed shape in its derived
category. -/
@[stacks 07D9 "derived coproducts"]
instance hasCoproductsOfShape_of_grothendieck
    [IsGrothendieckAbelian.{uJ} A] :
    HasCoproductsOfShape J (DerivedCategory A) :=
  hasCoproductsOfShape_of_exact

end CategoryTheory.DerivedCategory.Coproduct
