/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Definition_100_9_1_Immersion

/-!
# Image of an immersion as a locally closed substack

A locally closed, open, or closed substack of an algebraic stack `X` is an algebraic
stack `Y` equipped with a strictly full immersion `ι : Y ⟶ X`. The essential image of
an immersion is the canonical such subcategory, recovered as `objectProperty`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

variable {S : Scheme.{u}}

/-- A 1-morphism of categories fibred in groupoids presents a strictly full
subcategory of the target when its underlying total functor is fully faithful. -/
class IsStrictlyFull {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- The underlying total functor is full. -/
  full : (toFunctor f).Full
  /-- The underlying total functor is faithful. -/
  faithful : (toFunctor f).Faithful

namespace IsStrictlyFull

/-- The identity 1-morphism presents the ambient algebraic stack as a strictly
full subcategory of itself. -/
instance id {X : GroupoidsOver S} : IsStrictlyFull (𝟙 X) := sorry

/-- A strictly full 1-morphism has a full and faithful total functor. -/
theorem spec {X Y : GroupoidsOver S} (f : X ⟶ Y) [IsStrictlyFull f] :
    (toFunctor f).Full ∧ (toFunctor f).Faithful := sorry

/-- A 1-morphism is strictly full if and only if its total functor is full and
faithful. -/
theorem iff {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    IsStrictlyFull f ↔ (toFunctor f).Full ∧ (toFunctor f).Faithful := sorry

end IsStrictlyFull

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The inclusion of a full subcategory of the total category of `X`, as a
1-morphism of categories fibred in groupoids over `Over S`. The underlying total
functor is `P.ι`. -/
def inclusionOf (X : GroupoidsOver S) (P : ObjectProperty X.total)
    [Functor.IsFibered.InGroupoids (P.ι ⋙ X.p)] :
    ofFunctor (P.ι ⋙ X.p) ⟶ X :=
  ofBasedFunctor
    { toFunctor := P.ι
      w := sorry }

/-- The inclusion of a full subcategory presents a strictly full subcategory. -/
instance inclusionOf_isStrictlyFull (X : GroupoidsOver S)
    (P : ObjectProperty X.total)
    [Functor.IsFibered.InGroupoids (P.ι ⋙ X.p)] :
    IsStrictlyFull (inclusionOf X P) := sorry

/-- A locally closed substack of an algebraic stack `X` is an algebraic stack
`Y` equipped with a strictly full immersion `ι : Y ⟶ X`. -/
structure LocallyClosedSubstack (X : GroupoidsOver S) [AlgebraicStack X] where
  /-- The algebraic stack underlying the locally closed substack. -/
  Y : GroupoidsOver S
  /-- The inclusion of the locally closed substack. -/
  ι : Y ⟶ X
  /-- The included object is an algebraic stack. -/
  isAlgebraicStack : AlgebraicStack Y
  /-- The inclusion is an immersion. -/
  isImmersion : Immersion ι
  /-- The inclusion presents a strictly full subcategory of `X`. -/
  isStrictlyFull : IsStrictlyFull ι

namespace LocallyClosedSubstack

variable {X : GroupoidsOver S} [AlgebraicStack X]

/-- The underlying object of a locally closed substack is an algebraic stack. -/
instance instAlgebraicStack (X' : LocallyClosedSubstack X) : AlgebraicStack X'.Y :=
  X'.isAlgebraicStack

/-- The inclusion of a locally closed substack is an immersion. -/
instance instImmersion (X' : LocallyClosedSubstack X) : Immersion X'.ι :=
  X'.isImmersion

/-- The inclusion of a locally closed substack is strictly full. -/
instance instIsStrictlyFull (X' : LocallyClosedSubstack X) : IsStrictlyFull X'.ι :=
  X'.isStrictlyFull

/-- The locally closed substack of `X` determined by a strictly full immersion. -/
def ofι {Y : GroupoidsOver S} [AlgebraicStack Y] (ι : Y ⟶ X)
    [Immersion ι] [IsStrictlyFull ι] : LocallyClosedSubstack X where
  Y := Y
  ι := ι
  isAlgebraicStack := inferInstance
  isImmersion := inferInstance
  isStrictlyFull := inferInstance

/-- The subcategory of `X` recovered from a locally closed substack is the
essential image of its inclusion. -/
def objectProperty (X' : LocallyClosedSubstack X) : ObjectProperty X.total :=
  (toFunctor X'.ι).essImage

/-- `objectProperty` is the essential image of the inclusion. -/
theorem objectProperty_def (X' : LocallyClosedSubstack X) :
    X'.objectProperty = (toFunctor X'.ι).essImage := sorry

/-- A locally closed substack is an algebraic stack with a strictly full
immersion into `X`. -/
theorem spec (X' : LocallyClosedSubstack X) :
    AlgebraicStack X'.Y ∧ Immersion X'.ι ∧ IsStrictlyFull X'.ι := sorry

/-- The essential image of a 1-morphism of categories fibred in groupoids, as a
replete full subcategory of the target total category. -/
abbrev imageObjects {Z : GroupoidsOver S} (i : Z ⟶ X) : ObjectProperty X.total :=
  (toFunctor i).essImage

/-- The restricted projection of the essential image of a 1-morphism remains
fibred in groupoids. -/
instance instIsFiberedInGroupoids_imageObjects {Z : GroupoidsOver S} (i : Z ⟶ X) :
    Functor.IsFibered.InGroupoids ((imageObjects i).ι ⋙ X.p) := sorry

/-- The essential image of an immersion is itself an algebraic stack. -/
instance instAlgebraicStack_imageObjects {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ X) [Immersion i] :
    AlgebraicStack (ofFunctor ((imageObjects i).ι ⋙ X.p)) := sorry

/-- The inclusion of the essential image of an immersion is an immersion. -/
instance instImmersion_imageObjects {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ X) [Immersion i] :
    Immersion (inclusionOf X (imageObjects i)) := sorry

/-- The unique locally closed substack of `X` through which an immersion `i`
factors up to equivalence. -/
def image {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ X) [Immersion i] :
    LocallyClosedSubstack X :=
  ofι (inclusionOf X (imageObjects i))

/-- The objects of `image i` are the essential image of `i`. -/
theorem image_objectProperty {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ X) [Immersion i] :
    (image i).objectProperty = imageObjects i := sorry

/-- The equivalence `i' : Z ⟶ image i` in the canonical factorization of an
immersion. The underlying total functor is `toEssImage`. -/
def imageLift {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ X)
    [Immersion i] : Z ⟶ (image i).Y :=
  ofBasedFunctor
    { toFunctor := (toFunctor i).toEssImage
      w := sorry }

/-- The canonical factorization map of an immersion is an equivalence of
categories fibred in groupoids. -/
instance imageLift_isEquivalence {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ X) [Immersion i] :
    (toBasedFunctor (imageLift i)).IsEquivalence := sorry

/-- An immersion equals the composite of `imageLift` with the inclusion of its
image substack. -/
theorem imageLift_comp {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ X)
    [Immersion i] : imageLift i ≫ (image i).ι = i := sorry

/-- A locally closed substack through which an immersion factors by an
equivalence has the same object property as the essential image. -/
theorem unique {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ X)
    [Immersion i] {X' : LocallyClosedSubstack X} {i' : Z ⟶ X'.Y}
    (h_equiv : (toBasedFunctor i').IsEquivalence)
    (h_fac : i' ≫ X'.ι = i) : X'.objectProperty = imageObjects i := sorry

end LocallyClosedSubstack

/-- An open substack of an algebraic stack `X` is an algebraic stack `Y`
equipped with a strictly full open immersion `ι : Y ⟶ X`. -/
structure OpenSubstack (X : GroupoidsOver S) [AlgebraicStack X] where
  /-- The algebraic stack underlying the open substack. -/
  Y : GroupoidsOver S
  /-- The inclusion of the open substack. -/
  ι : Y ⟶ X
  /-- The included object is an algebraic stack. -/
  isAlgebraicStack : AlgebraicStack Y
  /-- The inclusion is an open immersion. -/
  isOpenImmersion : OpenImmersion ι
  /-- The inclusion presents a strictly full subcategory of `X`. -/
  isStrictlyFull : IsStrictlyFull ι

namespace OpenSubstack

variable {X : GroupoidsOver S} [AlgebraicStack X]

/-- The underlying object of an open substack is an algebraic stack. -/
instance instAlgebraicStack (U : OpenSubstack X) : AlgebraicStack U.Y :=
  U.isAlgebraicStack

/-- The inclusion of an open substack is an open immersion. -/
instance instOpenImmersion (U : OpenSubstack X) : OpenImmersion U.ι :=
  U.isOpenImmersion

/-- The inclusion of an open substack is strictly full. -/
instance instIsStrictlyFull (U : OpenSubstack X) : IsStrictlyFull U.ι :=
  U.isStrictlyFull

/-- The open substack of `X` determined by a strictly full open immersion. -/
def ofι {Y : GroupoidsOver S} [AlgebraicStack Y] (ι : Y ⟶ X)
    [OpenImmersion ι] [IsStrictlyFull ι] : OpenSubstack X where
  Y := Y
  ι := ι
  isAlgebraicStack := inferInstance
  isOpenImmersion := inferInstance
  isStrictlyFull := inferInstance

/-- The subcategory of `X` recovered from an open substack is the essential
image of its inclusion. -/
def objectProperty (U : OpenSubstack X) : ObjectProperty X.total :=
  (toFunctor U.ι).essImage

/-- `objectProperty` is the essential image of the inclusion. -/
theorem objectProperty_def (U : OpenSubstack X) :
    U.objectProperty = (toFunctor U.ι).essImage := sorry

/-- An open substack is an algebraic stack with a strictly full open immersion
into `X`. -/
theorem spec (U : OpenSubstack X) :
    AlgebraicStack U.Y ∧ OpenImmersion U.ι ∧ IsStrictlyFull U.ι := sorry

/-- Forget that an open substack is open, retaining the locally closed substack. -/
def toLocallyClosed (U : OpenSubstack X) : LocallyClosedSubstack X :=
  LocallyClosedSubstack.ofι U.ι

/-- The inclusion of the essential image of an open immersion is an open
immersion. -/
instance instOpenImmersion_imageObjects {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ X) [OpenImmersion i] :
    OpenImmersion (inclusionOf X (LocallyClosedSubstack.imageObjects i)) := sorry

/-- The unique open substack of `X` through which an open immersion factors up
to equivalence. -/
def image {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ X)
    [OpenImmersion i] : OpenSubstack X :=
  ofι (inclusionOf X (LocallyClosedSubstack.imageObjects i))

/-- The objects of `OpenSubstack.image i` are the essential image of `i`. -/
theorem image_objectProperty {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ X) [OpenImmersion i] :
    (image i).objectProperty = LocallyClosedSubstack.imageObjects i := sorry

end OpenSubstack

/-- A closed substack of an algebraic stack `X` is an algebraic stack `Y`
equipped with a strictly full closed immersion `ι : Y ⟶ X`. -/
structure ClosedSubstack (X : GroupoidsOver S) [AlgebraicStack X] where
  /-- The algebraic stack underlying the closed substack. -/
  Y : GroupoidsOver S
  /-- The inclusion of the closed substack. -/
  ι : Y ⟶ X
  /-- The included object is an algebraic stack. -/
  isAlgebraicStack : AlgebraicStack Y
  /-- The inclusion is a closed immersion. -/
  isClosedImmersion : ClosedImmersion ι
  /-- The inclusion presents a strictly full subcategory of `X`. -/
  isStrictlyFull : IsStrictlyFull ι

namespace ClosedSubstack

variable {X : GroupoidsOver S} [AlgebraicStack X]

/-- The underlying object of a closed substack is an algebraic stack. -/
instance instAlgebraicStack (Z' : ClosedSubstack X) : AlgebraicStack Z'.Y :=
  Z'.isAlgebraicStack

/-- The inclusion of a closed substack is a closed immersion. -/
instance instClosedImmersion (Z' : ClosedSubstack X) : ClosedImmersion Z'.ι :=
  Z'.isClosedImmersion

/-- The inclusion of a closed substack is strictly full. -/
instance instIsStrictlyFull (Z' : ClosedSubstack X) : IsStrictlyFull Z'.ι :=
  Z'.isStrictlyFull

/-- The closed substack of `X` determined by a strictly full closed immersion. -/
def ofι {Y : GroupoidsOver S} [AlgebraicStack Y] (ι : Y ⟶ X)
    [ClosedImmersion ι] [IsStrictlyFull ι] : ClosedSubstack X where
  Y := Y
  ι := ι
  isAlgebraicStack := inferInstance
  isClosedImmersion := inferInstance
  isStrictlyFull := inferInstance

/-- The subcategory of `X` recovered from a closed substack is the essential
image of its inclusion. -/
def objectProperty (Z' : ClosedSubstack X) : ObjectProperty X.total :=
  (toFunctor Z'.ι).essImage

/-- `objectProperty` is the essential image of the inclusion. -/
theorem objectProperty_def (Z' : ClosedSubstack X) :
    Z'.objectProperty = (toFunctor Z'.ι).essImage := sorry

/-- A closed substack is an algebraic stack with a strictly full closed
immersion into `X`. -/
theorem spec (Z' : ClosedSubstack X) :
    AlgebraicStack Z'.Y ∧ ClosedImmersion Z'.ι ∧ IsStrictlyFull Z'.ι := sorry

/-- Forget that a closed substack is closed, retaining the locally closed substack. -/
def toLocallyClosed (Z' : ClosedSubstack X) : LocallyClosedSubstack X :=
  LocallyClosedSubstack.ofι Z'.ι

/-- The inclusion of the essential image of a closed immersion is a closed
immersion. -/
instance instClosedImmersion_imageObjects {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ X) [ClosedImmersion i] :
    ClosedImmersion (inclusionOf X (LocallyClosedSubstack.imageObjects i)) := sorry

/-- The unique closed substack of `X` through which a closed immersion factors
up to equivalence. -/
def image {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ X)
    [ClosedImmersion i] : ClosedSubstack X :=
  ofι (inclusionOf X (LocallyClosedSubstack.imageObjects i))

/-- The objects of `ClosedSubstack.image i` are the essential image of `i`. -/
theorem image_objectProperty {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ X) [ClosedImmersion i] :
    (image i).objectProperty = LocallyClosedSubstack.imageObjects i := sorry

end ClosedSubstack

namespace LocallyClosedSubstack

variable {X : GroupoidsOver S} [AlgebraicStack X]

/-- Convert a locally closed substack whose inclusion is an open immersion into an
open substack. -/
def toOpen (X' : LocallyClosedSubstack X) [OpenImmersion X'.ι] :
    OpenSubstack X :=
  OpenSubstack.ofι X'.ι

/-- Convert a locally closed substack whose inclusion is a closed immersion into a
closed substack. -/
def toClosed (X' : LocallyClosedSubstack X) [ClosedImmersion X'.ι] :
    ClosedSubstack X :=
  ClosedSubstack.ofι X'.ι

end LocallyClosedSubstack

end AlgebraicGeometry.AlgebraicStack
