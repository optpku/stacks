module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global generators detected on stalks

The concrete owner is the submodule spanned by the germs of a family of global sections.  The
main API identifies this span with the range of the corresponding free-sheaf morphism and hence
detects global generation stalkwise.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SheafOfModules.GeneratingSections

variable {Z : TopCat.{u}} {𝒪 : Z.Sheaf RingCat.{u}}
variable {ℱ : SheafOfModules 𝒪} {I : Type u}

/-- The submodule of the stalk at `x` spanned by the germs of a family of global sections. -/
@[stacks 01AN "stalk span"]
noncomputable def stalkSpan (s : I → ℱ.sections) (x : Z) :
    Submodule (𝒪.presheaf.stalk x) ((stalkFunctor 𝒪 x).obj ℱ) :=
  Submodule.span (𝒪.presheaf.stalk x) (Set.range fun i ↦ sectionGerm (s i) x)

/-- The range of the stalk map induced by a family of global sections is exactly its stalk
span. -/
theorem stalkMap_range_eq_stalkSpan (s : I → ℱ.sections) (x : Z) :
    ((stalkFunctor 𝒪 x).map (ℱ.freeHomEquiv.symm s)).hom.range = stalkSpan s x := sorry

/-- Lemma 17.4.2, for a sheaf of modules over an arbitrary ring sheaf: a family of global
sections generates the sheaf exactly when its germs span every stalk. -/
@[stacks 01AN "ring-sheaf form"]
theorem epi_iff_stalkSpan_eq_top (s : I → ℱ.sections) :
    Epi (ℱ.freeHomEquiv.symm s) ↔ ∀ x : Z, stalkSpan s x = ⊤ := sorry

/-- The germs of a chosen family of global generators span every stalk. -/
theorem stalkSpan_eq_top (σ : ℱ.GeneratingSections) :
    ∀ x : Z, stalkSpan σ.s x = ⊤ := sorry

namespace CommRing

variable {𝒪 : Z.Sheaf CommRingCat.{u}}
variable {ℱ : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)} {I : Type u}

/-- The submodule of a commutative-ring stalk spanned by the germs of a family of global
sections. -/
@[stacks 01AN "commutative stalk span"]
noncomputable def stalkSpan (s : I → ℱ.sections) (x : Z) :
    Submodule (𝒪.presheaf.stalk x) ((stalkFunctorOfCommRing 𝒪 x).obj ℱ) :=
  Submodule.span (𝒪.presheaf.stalk x)
    (Set.range fun i ↦ sectionGermOfCommRing (s i) x)

/-- The range of the commutative-ring stalk map induced by a family of global sections is
exactly its stalk span. -/
theorem stalkMap_range_eq_stalkSpan (s : I → ℱ.sections) (x : Z) :
    ((stalkFunctorOfCommRing 𝒪 x).map (ℱ.freeHomEquiv.symm s)).hom.range =
      stalkSpan s x := sorry

/-- Lemma 17.4.2: a family of global sections over a commutative-ring sheaf generates the sheaf
exactly when its germs span every stalk. -/
@[stacks 01AN]
theorem epi_iff_stalkSpan_eq_top (s : I → ℱ.sections) :
    Epi (ℱ.freeHomEquiv.symm s) ↔ ∀ x : Z, stalkSpan s x = ⊤ := sorry

/-- The germs of a chosen family of global generators over a commutative-ring sheaf span every
stalk. -/
theorem stalkSpan_eq_top (σ : ℱ.GeneratingSections) :
    ∀ x : Z, stalkSpan σ.s x = ⊤ := sorry

end CommRing

end SheafOfModules.GeneratingSections

namespace SheafOfModules.Free

variable {Z : TopCat.{u}}

/-- The germs of the tautological global sections span the stalk of a free module sheaf. -/
theorem stalkSpan_eq_top
    (𝒪 : Z.Sheaf RingCat.{u}) (I : Type u) (x : Z) :
    GeneratingSections.stalkSpan
      (ℱ := free (R := 𝒪) I) (I := I) (freeSection (R := 𝒪)) x = ⊤ := sorry

/-- Over a commutative-ring sheaf, the germs of the tautological global sections span every
stalk of a free module sheaf. -/
theorem stalkSpanOfCommRing_eq_top
    (𝒪 : Z.Sheaf CommRingCat.{u}) (I : Type u) (x : Z) :
    GeneratingSections.CommRing.stalkSpan
      (ℱ := free (R := TopCat.Sheaf.ringSheafOfComm 𝒪) I) (I := I)
      (freeSection (R := TopCat.Sheaf.ringSheafOfComm 𝒪)) x = ⊤ := sorry

end SheafOfModules.Free
