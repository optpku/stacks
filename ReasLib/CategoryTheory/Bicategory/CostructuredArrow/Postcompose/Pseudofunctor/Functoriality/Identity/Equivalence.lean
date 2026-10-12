/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Iso
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality.Identity.Component
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Basic

/-!
# Objectwise equivalence for identity postcomposition

This leaf upgrades the explicit identity-postcomposition components to an
equivalence of individual colax costructured arrows. Strong naturality is kept
separate for reuse at the object-transport level.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X : C}

namespace Implementation

/-- The source-map isomorphism of the identity-postcomposition component unit. -/
private def postcompose.identity.component.unit.sourceIso
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := X)
        (𝟙 (postcompose.obj (𝟙 X) S)) ≅
      ColaxCostructuredArrow.map (K := K) (X := X)
        (postcompose.identity.component.hom S ≫
          postcompose.identity.component.inv S) :=
  (λ_ (𝟙 S.left)).symm

/-- Compatibility of the identity-postcomposition unit source-map isomorphism
with normalized comparisons. -/
private theorem postcompose.identity.component.unit.comm
    (S : ColaxCostructuredArrow K X) :
    ((postcompose.obj (𝟙 X) S).comparison S.left).map
          (postcompose.identity.component.unit.sourceIso S).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := X)
          (postcompose.identity.component.hom S ≫
            postcompose.identity.component.inv S) =
      ColaxCostructuredArrow.fac (K := K) (X := X)
        (𝟙 (postcompose.obj (𝟙 X) S)) := sorry

/-- The source-map isomorphism of the identity-postcomposition component
counit. -/
private def postcompose.identity.component.counit.sourceIso
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := X)
        (postcompose.identity.component.inv S ≫
          postcompose.identity.component.hom S) ≅
      ColaxCostructuredArrow.map (K := K) (X := X) (𝟙 S) :=
  λ_ (𝟙 S.left)

/-- Compatibility of the identity-postcomposition counit source-map
isomorphism with normalized comparisons. -/
private theorem postcompose.identity.component.counit.comm
    (S : ColaxCostructuredArrow K X) :
    (S.comparison S.left).map
          (postcompose.identity.component.counit.sourceIso S).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := X) (𝟙 S) =
      ColaxCostructuredArrow.fac (K := K) (X := X)
        (postcompose.identity.component.inv S ≫
          postcompose.identity.component.hom S) := sorry

end Implementation

/-- The unit isomorphism for the identity-postcomposition components. -/
def postcompose.identity.component.unit
    (S : ColaxCostructuredArrow K X) :
    𝟙 (postcompose.obj (𝟙 X) S) ≅
      postcompose.identity.component.hom S ≫
        postcompose.identity.component.inv S :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.postcompose.identity.component.unit.sourceIso S)
    (Implementation.postcompose.identity.component.unit.comm S)

/-- The counit isomorphism for the identity-postcomposition components. -/
def postcompose.identity.component.counit
    (S : ColaxCostructuredArrow K X) :
    postcompose.identity.component.inv S ≫
        postcompose.identity.component.hom S ≅
      𝟙 S :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.postcompose.identity.component.counit.sourceIso S)
    (Implementation.postcompose.identity.component.counit.comm S)

/-- The objectwise equivalence from postcomposition by `𝟙 X` to the original
colax costructured arrow. -/
def postcompose.identity.component.equivalence
    (S : ColaxCostructuredArrow K X) :
    postcompose.obj (𝟙 X) S ≌ S :=
  Bicategory.Equivalence.mkOfAdjointifyUnit
    (postcompose.identity.component.unit S)
    (postcompose.identity.component.counit S)

/-- The forward morphism of the objectwise identity-postcomposition
equivalence is the explicit forward component. -/
@[simp]
theorem postcompose.identity.component.equivalence.hom
    (S : ColaxCostructuredArrow K X) :
    (postcompose.identity.component.equivalence S).hom =
      postcompose.identity.component.hom S := sorry

/-- The inverse morphism of the objectwise identity-postcomposition
equivalence is the explicit reverse component. -/
@[simp]
theorem postcompose.identity.component.equivalence.inv
    (S : ColaxCostructuredArrow K X) :
    (postcompose.identity.component.equivalence S).inv =
      postcompose.identity.component.inv S := sorry

/-- The unit of the objectwise identity-postcomposition equivalence is the
canonical adjointification of its explicit unit and counit candidates. -/
@[simp]
theorem postcompose.identity.component.equivalence.unit
    (S : ColaxCostructuredArrow K X) :
    (postcompose.identity.component.equivalence S).unit =
      Bicategory.Equivalence.adjointifyUnit
        (postcompose.identity.component.unit S)
        (postcompose.identity.component.counit S) := sorry

/-- The counit of the objectwise identity-postcomposition equivalence is the
explicit counit candidate. -/
@[simp]
theorem postcompose.identity.component.equivalence.counit
    (S : ColaxCostructuredArrow K X) :
    (postcompose.identity.component.equivalence S).counit =
      postcompose.identity.component.counit S := sorry

/- Data and axiom audit (mathlib 4.32):

The forward and inverse maps of `postcompose.identity.component.equivalence` are the
explicit components from the preceding leaf. `mkOfAdjointifyUnit` canonically
adjusts the candidate unit against the supplied counit; the public unit and
counit readout theorems expose the resulting data. Deferred obligations are
normalized-comparison compatibility and triangle/coherence laws; no non-Prop
component is hidden. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
