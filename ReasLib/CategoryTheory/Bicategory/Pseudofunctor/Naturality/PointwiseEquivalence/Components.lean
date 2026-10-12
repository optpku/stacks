/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Equivalence.OnHom
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Components

/-!
# Pointwise equivalence data for strong transformations

This leaf owns the componentwise data tied to a fixed forward strong
transformation and the bridge to pointwise adjunction data. Componentwise
constructors, actions, inverses, and assembled equivalences live in separate
leaves.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G : Pseudofunctor B D}

/-- Chosen pointwise adjoint-equivalence data on a strong transformation.

The forward morphism at `a` is fixed to be `η.app a`; this family supplies only its chosen
inverse, unit, counit, and triangle identity. Keeping the data tied to `η` avoids a duplicate
forward transformation and the equality transports required by an unrelated family
`F.obj a ≌ G.obj a`. -/
@[stacks 0040 "pointwise equivalence data on a strong transformation"]
abbrev PointwiseEquivalence (η : F ⟶ G) :=
  ∀ a : B, Bicategory.Equivalence.OnHom (η.app a)

namespace PointwiseEquivalence

variable {η : F ⟶ G}

/-- The fixed-morphism equivalence data carried at a source object. -/
@[stacks 0040 "fixed-morphism component data of a pointwise equivalence"]
def onHom (h : PointwiseEquivalence η) (a : B) :
    Bicategory.Equivalence.OnHom (η.app a) :=
  h a

/-- The chosen inverse to the component of `η` at a source object. -/
def invApp (h : PointwiseEquivalence η) (a : B) :
    G.obj a ⟶ F.obj a :=
  (h.onHom a).inv

/-- The unit of the chosen equivalence at a source object. -/
def unit (h : PointwiseEquivalence η) (a : B) :
    𝟙 (F.obj a) ≅ η.app a ≫ h.invApp a :=
  (h.onHom a).unit

/-- The counit of the chosen equivalence at a source object. -/
def counit (h : PointwiseEquivalence η) (a : B) :
    h.invApp a ≫ η.app a ≅ 𝟙 (G.obj a) :=
  (h.onHom a).counit

/-- The pointwise unit and counit satisfy the left triangle identity. -/
theorem left_triangle (h : PointwiseEquivalence η) (a : B) :
    Bicategory.leftZigzagIso (h.unit a) (h.counit a) =
      λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm := sorry

/-- The bicategorical equivalence carried by a pointwise-equivalence structure at a source
object. -/
@[stacks 0040 "component equivalence of a pointwise equivalence"]
def app (h : PointwiseEquivalence η) (a : B) :
    F.obj a ≌ G.obj a :=
  (h.onHom a).toEquivalence

/-- The forward morphism of the equivalence carried at `a` is `η.app a`. -/
@[simp]
theorem app.hom (h : PointwiseEquivalence η) (a : B) :
    (h.app a).hom = η.app a := sorry

/-- The inverse morphism of the equivalence carried at `a` is `h.invApp a`. -/
@[simp]
theorem app.inv (h : PointwiseEquivalence η) (a : B) :
    (h.app a).inv = h.invApp a := sorry

/-- The unit of the equivalence carried at `a` is `h.unit a`. -/
@[simp]
theorem app.unit (h : PointwiseEquivalence η) (a : B) :
    (h.app a).unit = h.unit a := sorry

/-- The counit of the equivalence carried at `a` is `h.counit a`. -/
@[simp]
theorem app.counit (h : PointwiseEquivalence η) (a : B) :
    (h.app a).counit = h.counit a := sorry

/-- Forget pointwise invertibility while retaining the chosen component adjunctions. -/
@[stacks 0040 "underlying pointwise adjunction of a pointwise equivalence"]
def toPointwiseAdjunction (h : PointwiseEquivalence η) :
    PointwiseAdjunction η := fun a ↦
  (h.onHom a).toRightAdjoint

/-- The pointwise right adjoint is unchanged when forgetting invertibility. -/
@[simp]
theorem toPointwiseAdjunction.rightApp
    (h : PointwiseEquivalence η) (a : B) :
    h.toPointwiseAdjunction.rightApp a = h.invApp a := sorry

/-- The pointwise adjunction obtained by forgetting invertibility is the adjunction underlying
the component equivalence. -/
@[simp]
theorem toPointwiseAdjunction.adj
    (h : PointwiseEquivalence η) (a : B) :
    h.toPointwiseAdjunction.adj a =
      (h.app a).toAdjunction := sorry

/- Data audit (mathlib 4.32): `PointwiseEquivalence` is a family of the generic
fixed-morphism owner `Bicategory.Equivalence.OnHom`. `app` and
`toPointwiseAdjunction` only repackage that chosen data. Any `sorryAx` is
confined to triangle or projection propositions. -/

end PointwiseEquivalence

end Pseudofunctor.StrongTrans

end CategoryTheory
