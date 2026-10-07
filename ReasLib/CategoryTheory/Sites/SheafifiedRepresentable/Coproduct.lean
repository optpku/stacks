module

public import ReasLib.CategoryTheory.Sites.Family
public import ReasLib.CategoryTheory.Sites.Sheaf.Types.Colimits
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Coproducts of sheafified representables

This leaf owns the canonical coproduct of the sheafified representables attached
to an indexed family of objects. Finiteness is a property of a family and belongs
in the statements that require it, rather than in the coproduct construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The coproduct of the sheafified representables attached to an indexed family. -/
noncomputable def sheafifiedRepresentableCoproduct
    [HasWeakSheafify J (Type (max w u v))]
    (𝒰 : Limits.FormalCoproduct.{w} C) :
    Sheaf J (Type (max w u v)) :=
  ∐ fun i : 𝒰.index ↦ J.uliftSheafifiedRepresentable.{w} (𝒰.obj i)

end CategoryTheory.GrothendieckTopology
