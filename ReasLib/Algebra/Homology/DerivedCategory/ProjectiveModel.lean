module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective models of bounded-above derived objects

In an abelian category with enough projectives, a cohomologically bounded-above derived object has
a bounded-above termwise-projective representative.  The existential model is the reusable bridge
between t-structure bounds and `CochainComplex.ProjectiveMinus` computations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory.IsLE

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory.{w} C]
variable {K : DerivedCategory C}

/-- Stacks `0646`: a cohomologically bounded-above derived object admits a projective-minus model. -/
@[stacks 0646 "projective-minus model of a bounded-above derived object"]
theorem exists_projective_model [EnoughProjectives C] {b : ℤ} (hK : K.IsLE b) :
    ∃ P : CochainComplex.ProjectiveMinus C,
      IsIsomorphic (DerivedCategory.Q.obj (P : CochainComplex C ℤ)) K := sorry

end CategoryTheory.DerivedCategory.IsLE

end
