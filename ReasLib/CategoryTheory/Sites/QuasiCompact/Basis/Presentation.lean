module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import ReasLib.CategoryTheory.Presentation.Finite
public import ReasLib.CategoryTheory.Sites.EnoughObjects.Presentation
public import ReasLib.CategoryTheory.Sites.QuasiCompact.Basis
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentations from a quasi-compact basis

Sheafified representables attached to a quasi-compact basis generate all set-valued sheaves under
filtered colimits of finite coequalizer presentations.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology.Basis

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (B : Set C)
variable [HasWeakSheafify J (Type (max u v))]

/-- Equation 18.30.7.1: the property of admitting a finite coequalizer presentation by
sheafified representables attached to objects of `B`. -/
@[stacks 09Y7]
abbrev finiteSheafPresentation : ObjectProperty (Sheaf J (Type (max u v))) :=
  J.sheafifiedRepresentableFunctor.finiteCoequalizerPresentation B

/-- Lemma 18.30.7 (093C) (1), sieve-saturated specialization: enough basis objects and
Grothendieck-topology quasi-compactness generate every sheaf by finite `B`-presentations. -/
@[stacks 093C "(1), sieve-saturated specialization"]
theorem finiteSheafPresentation_ind
    (h_enough : J.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (h_compact : IsQuasiCompact J B) (F : Sheaf J (Type (max u v))) :
    (finiteSheafPresentation J B).ind F := sorry

end CategoryTheory.GrothendieckTopology.Basis

namespace CategoryTheory.Coverage.Basis

variable {C : Type u} [Category.{v} C] (K : Coverage C) (B : Set C)
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]

/-- Lemma 18.30.7 (093C) (1): if a chosen-cover site has enough objects in `B` and those
objects are quasi-compact, every sheaf of sets is a filtered colimit of finite
`B`-presentations. -/
@[stacks 093C "(1)"]
theorem finiteSheafPresentationInd
    (hEnough : K.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (hCompact : IsQuasiCompact K B)
    (F : Sheaf K.toGrothendieck (Type (max u v))) :
    (GrothendieckTopology.Basis.finiteSheafPresentation K.toGrothendieck B).ind F := sorry

end CategoryTheory.Coverage.Basis
