/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import ReasLib.Algebra.Homology.HomologicalComplex.Admissible
public import ReasLib.Algebra.Homology.HomologicalComplex.TermwiseSplit
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Splittings over termwise projective targets

A morphism of homological complexes which is epic in every degree admits a section after
forgetting the differential whenever its target is projective in every degree.  The chosen section
is explicit data; admissibility and termwise splitness are downstream properties, not instances.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomologicalComplex.ProjectiveTarget

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type w} {c : ComplexShape ι}
variable {K L : HomologicalComplex C c}

/-- The chosen lift of the identity in degree `i` through a componentwise epimorphism whose
target is projective in that degree. -/
noncomputable def component (f : K ⟶ L) (h_epi : ∀ i, Epi (f.f i))
    (h_projective : ∀ i, Projective (L.X i)) (i : ι) : L.X i ⟶ K.X i :=
  @Projective.factorThru C _ (L.X i) (L.X i) (K.X i) (h_projective i)
    (𝟙 (L.X i)) (f.f i) (h_epi i)

/-- The section of the underlying graded morphism obtained by lifting the identity independently
in every degree. -/
noncomputable def section_ (f : K ⟶ L) (h_epi : ∀ i, Epi (f.f i))
    (h_projective : ∀ i, Projective (L.X i)) :
    (forget C c).obj L ⟶ (forget C c).obj K :=
  fun i ↦ component f h_epi h_projective i

/-- Evaluation of the underlying graded section is the chosen projective lift in that degree. -/
@[simp]
theorem section_apply (f : K ⟶ L) (h_epi : ∀ i, Epi (f.f i))
    (h_projective : ∀ i, Projective (L.X i)) (i : ι) :
    section_ f h_epi h_projective i = component f h_epi h_projective i := sorry

/-- Each chosen component is a right inverse to the corresponding component of the original
morphism. -/
@[reassoc (attr := simp)]
theorem component_comp (f : K ⟶ L) (h_epi : ∀ i, Epi (f.f i))
    (h_projective : ∀ i, Projective (L.X i)) (i : ι) :
    component f h_epi h_projective i ≫ f.f i = 𝟙 (L.X i) := sorry

/-- The chosen graded section is a right inverse after forgetting the differential. -/
@[reassoc (attr := simp)]
theorem section_comp (f : K ⟶ L) (h_epi : ∀ i, Epi (f.f i))
    (h_projective : ∀ i, Projective (L.X i)) :
    section_ f h_epi h_projective ≫ (forget C c).map f = 𝟙 ((forget C c).obj L) := sorry

/-- A componentwise epimorphism onto a termwise projective complex is termwise split epic. -/
theorem termwiseSplitEpi (f : K ⟶ L) (h_epi : ∀ i, Epi (f.f i))
    (h_projective : ∀ i, Projective (L.X i)) :
    HomologicalComplex.termwiseSplitEpi C c f := sorry

/-- A componentwise epimorphism onto a termwise projective complex is admissibly epic for the
functor which forgets the differential. -/
theorem admissibleEpi (f : K ⟶ L) (h_epi : ∀ i, Epi (f.f i))
    (h_projective : ∀ i, Projective (L.X i)) :
    IsAdmissibleEpi (forget C c) f := sorry

end HomologicalComplex.ProjectiveTarget
