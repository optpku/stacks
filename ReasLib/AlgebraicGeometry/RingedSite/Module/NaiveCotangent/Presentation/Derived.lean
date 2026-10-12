/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Map

/-!
# Derived-category presentation models of the naive cotangent complex

This file keeps a polynomial presentation visible while exposing presentation independence at the
derived-category level. Explicit comparison morphisms belong to the functorial presentation API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.NaiveCotangent

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable {A : Sheaf J CommRingCat.{w}} {B : Under A}

namespace Presentation

/-- The two-term naive cotangent complex associated to the polynomial presentation of `B`
induced by a map from a sheaf of generators. -/
@[stacks 08TL "presentation model", stacks 08TY "presentation model"]
abbrev ofGenerators
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    CochainComplex (SheafOfModules (ringSheaf J B.right)) ℤ :=
  complex (FreeAlgebra.base A E) (FreeAlgebra.evaluation B E α).right

/-- Degree `-1` of a presentation model is the conormal source of its presentation map. -/
theorem ofGenerators_X_negOne
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    (ofGenerators E α).X (-1) =
      conormalSource (FreeAlgebra.evaluation B E α).right := sorry

/-- Degree `0` of a presentation model is its base-changed relative-differentials term. -/
theorem ofGenerators_X_zero
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    (ofGenerators E α).X 0 =
      conormalTensorTerm (FreeAlgebra.base A E) (FreeAlgebra.evaluation B E α).right := sorry

/-- The differential from degree `-1` to degree `0` in a presentation model is its conormal map. -/
theorem ofGenerators_d_negOne_zero
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    (ofGenerators E α).d (-1) 0 =
      differential (FreeAlgebra.base A E) (FreeAlgebra.evaluation B E α).right (-1) := sorry

/-- The map from a chosen free presenting algebra to the canonical free presenting algebra,
obtained by sending each chosen generator to its canonical bracket. -/
noncomputable def toCanonicalMiddle
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    FreeAlgebra.underlying A E ⟶ FreeAlgebra.Presentation.underlying A B :=
  (FreeAlgebra.evaluation (FreeAlgebra.Presentation.obj A B) E
    (α ≫ FreeAlgebra.Presentation.generator A B)).right

/-- The coefficient square for the map from a chosen presentation to the canonical presentation
commutes. -/
theorem toCanonicalMiddle_baseSq
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    CommSq (𝟙 A) (FreeAlgebra.base A E) (FreeAlgebra.Presentation.base A B)
      (toCanonicalMiddle E α) := sorry

/-- The evaluation square for the map from a chosen presentation to the canonical presentation
commutes. -/
theorem toCanonicalMiddle_targetSq
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    CommSq (toCanonicalMiddle E α) (FreeAlgebra.evaluation B E α).right
      (FreeAlgebra.Presentation.map A B) (𝟙 B.right) := sorry

/-- The canonical morphism from a chosen polynomial presentation to the canonical polynomial
presentation. -/
@[stacks 08TL "comparison of presentations", stacks 08TY "comparison of presentations"]
noncomputable def toCanonicalHom
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    Hom (FreeAlgebra.base A E) (FreeAlgebra.evaluation B E α).right
      (FreeAlgebra.Presentation.base A B) (FreeAlgebra.Presentation.map A B) where
  base := 𝟙 A
  middle := toCanonicalMiddle E α
  target := 𝟙 B.right
  baseSq := toCanonicalMiddle_baseSq E α
  targetSq := toCanonicalMiddle_targetSq E α

/-- The explicit cochain map from a chosen presentation model to the canonical naive cotangent
complex. -/
@[stacks 08TL "comparison map", stacks 08TY "comparison map"]
noncomputable def toCanonicalMap
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    ofGenerators E α ⟶ NaiveCotangent.obj A B :=
  (extendComplexIdIso B.right).inv.app (ofGenerators E α) ≫
    Hom.map (toCanonicalHom E α)

/-- The degreewise map of `toCanonicalMap` is the identity-extension comparison followed by
the corresponding component of the presentation map. -/
theorem toCanonicalMap_f
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) (n : ℤ) :
    (toCanonicalMap E α).f n =
      ((extendComplexIdIso B.right).inv.app (ofGenerators E α)).f n ≫
        (Hom.map (toCanonicalHom E α)).f n := sorry

/-- In degree `-1`, `toCanonicalMap` is the identity-extension comparison followed by the
conormal-term map of the canonical presentation morphism. -/
@[stacks 08TL "comparison in degree -1", stacks 08TY "comparison in degree -1"]
theorem toCanonicalMap_f_negOne
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    (toCanonicalMap E α).f (-1) =
      ((extendComplexIdIso B.right).inv.app (ofGenerators E α)).f (-1) ≫
        Hom.Conormal.map (toCanonicalHom E α) := sorry

/-- In degree `0`, `toCanonicalMap` is the identity-extension comparison followed by the
differential-term map of the canonical presentation morphism. -/
@[stacks 08TL "comparison in degree 0", stacks 08TY "comparison in degree 0"]
theorem toCanonicalMap_f_zero
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    (toCanonicalMap E α).f 0 =
      ((extendComplexIdIso B.right).inv.app (ofGenerators E α)).f 0 ≫
        Hom.Differentials.map (toCanonicalHom E α) := sorry

variable [HasDerivedCategory (SheafOfModules (ringSheaf J B.right))]

/-- The canonical comparison in the derived category from a chosen presentation model to the
canonical naive cotangent complex. -/
@[stacks 08TL "derived comparison morphism", stacks 08TY "derived comparison morphism"]
noncomputable def derivedComparison
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    DerivedCategory.Q.obj (ofGenerators E α) ⟶
      DerivedCategory.Q.obj (NaiveCotangent.obj A B) :=
  DerivedCategory.Q.map (toCanonicalMap E α)

/-- The derived comparison is the image of the explicit presentation comparison map. -/
@[simp]
theorem derivedComparison_spec
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B) :
    derivedComparison E α = DerivedCategory.Q.map (toCanonicalMap E α) := sorry

/-- A locally surjective polynomial presentation gives an invertible canonical comparison in the
derived category. -/
@[stacks 08TL "derived comparison is an isomorphism",
  stacks 08TY "derived comparison is an isomorphism"]
instance derivedComparison_isIso
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation B E α).right] :
    IsIso (derivedComparison E α) := sorry

/-- The explicit inverse of the derived presentation comparison. -/
@[stacks 08TL "derived comparison inverse", stacks 08TY "derived comparison inverse"]
noncomputable def derivedComparisonInv
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation B E α).right] :
    DerivedCategory.Q.obj (NaiveCotangent.obj A B) ⟶
      DerivedCategory.Q.obj (ofGenerators E α) :=
  inv (derivedComparison E α)

/-- The derived presentation comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 08TL "derived comparison forward-inverse law",
  stacks 08TY "derived comparison forward-inverse law"]
theorem derivedComparison_comp_derivedComparisonInv
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation B E α).right] :
    derivedComparison E α ≫ derivedComparisonInv E α = 𝟙 _ := sorry

/-- The explicit inverse followed by the derived presentation comparison is the identity. -/
@[simp, stacks 08TL "derived comparison inverse-forward law",
  stacks 08TY "derived comparison inverse-forward law"]
theorem derivedComparisonInv_comp_derivedComparison
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation B E α).right] :
    derivedComparisonInv E α ≫ derivedComparison E α = 𝟙 _ := sorry

/-- The canonical derived isomorphism from a polynomial presentation whose evaluation map is
locally surjective to the naive cotangent complex. -/
@[stacks 08TL "evaluation-surjective comparison",
  stacks 08TY "evaluation-surjective comparison"]
noncomputable def derivedComparisonIso
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation B E α).right] :
    DerivedCategory.Q.obj (ofGenerators E α) ≅
      DerivedCategory.Q.obj (NaiveCotangent.obj A B) :=
  { hom := derivedComparison E α
    inv := derivedComparisonInv E α
    hom_inv_id := derivedComparison_comp_derivedComparisonInv E α
    inv_hom_id := derivedComparisonInv_comp_derivedComparison E α }

/-- The forward map of the derived presentation isomorphism is the canonical comparison. -/
@[simp]
theorem derivedComparisonIso_hom
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation B E α).right] :
    (derivedComparisonIso E α).hom = derivedComparison E α := sorry

/-- The inverse of the derived presentation isomorphism is the named explicit inverse. -/
@[simp, stacks 08TL "derived comparison isomorphism inverse",
  stacks 08TY "derived comparison isomorphism inverse"]
theorem derivedComparisonIso_inv
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation B E α).right] :
    (derivedComparisonIso E α).inv = derivedComparisonInv E α := sorry

/-- A locally surjective family of generators gives a canonical derived identification of its
polynomial presentation model with the naive cotangent complex. -/
@[stacks 08TL, stacks 08TY]
noncomputable def ofGeneratorsIso
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective α] :
    DerivedCategory.Q.obj (ofGenerators E α) ≅
      DerivedCategory.Q.obj (NaiveCotangent.obj A B) :=
  derivedComparisonIso E α

/-- The forward map of the generator-presentation isomorphism is the canonical derived
comparison. -/
@[simp]
theorem ofGeneratorsIso_hom
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective α] :
    (ofGeneratorsIso E α).hom = derivedComparison E α := sorry

/-- Compatibility corollary: a locally surjective polynomial presentation computes the
canonical naive cotangent complex in the derived category of `B`-module sheaves. -/
@[stacks 08TL "existence corollary", stacks 08TY "existence corollary"]
theorem isIsomorphic
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation B E α).right] :
    IsIsomorphic
      (DerivedCategory.Q.obj (ofGenerators E α))
      (DerivedCategory.Q.obj (NaiveCotangent.obj A B)) := sorry

end Presentation

end SheafOfModules.RingedSite.NaiveCotangent

-- The complex terms and differential are explicit; only their Prop-valued laws may use `sorryAx`.
