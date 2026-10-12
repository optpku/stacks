/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.Topos.Embedding

/-!
# Site-presented subtopoi

A subtopos is represented here by actual site-presentation data: a second
site, an embedding of its sheaf topos, and an identification of the requested
object property with the essential image of direct image.  The public
predicate only asserts that such data exists, without exposing an arbitrary
choice of presentation.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.GrothendieckTopology

/-- A site presentation of an object property as the essential image of the
direct image of an embedding of topoi. -/
structure SubtoposPresentation
    {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) (E : ObjectProperty (Sheaf J (Type w))) where
  /-- The site underlying the presented subtopos. -/
  D : Type u₂
  /-- The category structure on the presenting site. -/
  categoryD : Category.{v₂} D
  /-- The Grothendieck topology on the presenting site. -/
  K : @GrothendieckTopology D categoryD
  /-- The morphism of topoi whose direct image presents the subtopos. -/
  morphism : @MorphismOfTopoiIn C _ D categoryD J K
  /-- The presenting morphism is an embedding. -/
  isEmbedding : LeftExactAdjunction.IsEmbedding morphism
  /-- The requested object property is the essential image of direct image. -/
  essImage_eq : E = morphism.pushforward.essImage

/-- The essential image of an embedding of sheaf topoi, presented by its source site. -/
noncomputable def SubtoposPresentation.ofEmbedding
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)
    (f : MorphismOfTopoiIn J K) (h : f.IsEmbedding) :
    SubtoposPresentation J f.pushforward.essImage where
  D := D
  categoryD := inferInstance
  K := K
  morphism := f
  isEmbedding := h
  essImage_eq := rfl

/-- A strictly full subcategory of `Sh(C)` is a subtopos when it admits a site presentation by
the direct image of an embedding. -/
@[stacks 08LV]
def IsSubtopos
    {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) (E : ObjectProperty (Sheaf J (Type w))) : Prop :=
  Nonempty (SubtoposPresentation.{u₁, u₂, v₁, v₂, w} J E)

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The essential image of the direct image of an embedding of topoi is a
subtopos. -/
theorem isSubtopos_essImage (f : MorphismOfTopoiIn J K) [f.IsEmbedding] :
    GrothendieckTopology.IsSubtopos.{u₁, u₂, v₁, v₂, w} J f.pushforward.essImage := sorry

end CategoryTheory.MorphismOfTopoiIn

namespace CategoryTheory.GrothendieckTopology

/-- A site-presented subtopos is closed under isomorphisms. -/
theorem IsSubtopos.isClosedUnderIsomorphisms
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {E : ObjectProperty (Sheaf J (Type w))} (hE : IsSubtopos J E) :
    E.IsClosedUnderIsomorphisms := sorry

/-- The ambient sheaf topos is a subtopos of itself. -/
theorem isSubtopos_top
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) :
    IsSubtopos.{u₁, u₁, v₁, v₁, w} J (⊤ : ObjectProperty (Sheaf J (Type w))) := sorry

end CategoryTheory.GrothendieckTopology
