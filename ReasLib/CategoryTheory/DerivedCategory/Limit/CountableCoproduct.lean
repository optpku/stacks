module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.Countable
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Coproducts
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproducts in Derived Categories

This leaf contains only the countable `AB4` specialization.  The shape-generic exact-coproduct
API is owned by `ReasLib.CategoryTheory.DerivedCategory.Limit.Coproducts`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u uI

namespace CategoryTheory.DerivedCategory.Coproduct

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Stacks 0A5L: a derived category over an abelian category with exact countable coproducts
has countable coproducts. -/
@[stacks 0A5L]
instance hasCountableCoproducts_of_countableAB4
    [HasCountableCoproducts A] [CountableAB4 A] :
    HasCountableCoproducts (DerivedCategory A) := sorry

/-- For a countable family of complexes, its termwise coproduct and canonical coprojections form
a coproduct cofan after passage to any chosen derived localization under `CountableAB4`. -/
@[stacks 0A5L "countable termwise coproduct model"]
noncomputable def cofanIsColimit_of_countableAB4
    [HasCountableCoproducts A] [CountableAB4 A]
    {J : Type uI} [Countable J] (K : J → CochainComplex A ℤ) :
    IsColimit
      (Cofan.mk
        (DerivedCategory.Q.obj (∐ K))
        (fun j ↦ DerivedCategory.Q.map (Sigma.ι K j))) :=
  cofanIsColimit_of_termwise K

end CategoryTheory.DerivedCategory.Coproduct
