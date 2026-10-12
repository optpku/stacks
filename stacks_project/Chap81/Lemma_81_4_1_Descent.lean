/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_18_8_Topos

/-!
# Descent of small étale sheaves along an étale covering

An étale covering `{f i : Xᵢ i ⟶ X}` of algebraic spaces yields a covering of
`X_spaces,étale` by the maps to the terminal object. Pullback of small étale
sheaves along this covering is identified with descent data.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type u}
  {Xᵢ : ι → AlgebraicSpace S}

/-- The object of `X_spaces,étale` given by an étale morphism `f i : Xᵢ i ⟶ X`. -/
def etaleCoveringObj (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (f i) inferInstance

/-- The underlying algebraic space of `etaleCoveringObj f i` is `Xᵢ i`. -/
theorem etaleCoveringObj_left (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    (etaleCoveringObj f i).left = Xᵢ i :=
  sorry

/-- The structural morphism of `etaleCoveringObj f i` is `f i`. -/
theorem etaleCoveringObj_hom (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    (etaleCoveringObj f i).hom = f i :=
  sorry

/-- The structure morphism of `etaleCoveringObj f i` toward the terminal object of
`X_spaces,étale`. -/
def etaleCoveringToSelf (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    etaleCoveringObj f i ⟶ spacesEtaleSite.self X :=
  spacesEtaleSite.homToSelf (etaleCoveringObj f i)

/-- The underlying morphism of `etaleCoveringToSelf f i` is `f i`. -/
theorem etaleCoveringToSelf_left (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] (i : ι) :
    (etaleCoveringToSelf f i).left = f i :=
  sorry

/-- Descent data for étale sheaves of types along the covering `{f i : Xᵢ i ⟶ X}`
in `X_spaces,étale`. -/
abbrev etaleCoveringDescent (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] :=
  ((spacesEtaleTopology X).pseudofunctorOver (Type (u + 1))).DescentData
    (fun i ↦ etaleCoveringToSelf f i)

/-- The functor sending a small étale sheaf on `X` to its descent datum along an
étale covering `{f i : Xᵢ i ⟶ X}`. -/
def sheafToEtaleCoveringDescent (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)] :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ etaleCoveringDescent f :=
  smallEtaleInclusionDirectImage X ⋙
    (spacesEtaleTopology X).overPullback (Type (u + 1)) (spacesEtaleSite.self X) ⋙
      ((spacesEtaleTopology X).pseudofunctorOver (Type (u + 1))).toDescentData
        (fun i ↦ etaleCoveringToSelf f i)

/-- The object map of `sheafToEtaleCoveringDescent f` is restriction to the slice
over the terminal object, followed by `toDescentData` of the covering. -/
theorem sheafToEtaleCoveringDescent_obj (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (sheafToEtaleCoveringDescent f).obj F =
      (((spacesEtaleTopology X).pseudofunctorOver (Type (u + 1))).toDescentData
          (fun i ↦ etaleCoveringToSelf f i)).obj
        (((spacesEtaleTopology X).overPullback (Type (u + 1))
            (spacesEtaleSite.self X)).obj
          ((smallEtaleInclusionDirectImage X).obj F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
