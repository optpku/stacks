module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoCone.Hom
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Construction

/-!
# Basic morphism projections for readable pseudopullback cones

This leaf gives the readable four-field presentation its bicategory structure and exposes the
apex, comparison, and leg-cell projections of its morphisms and `2`-morphisms. The structure is
induced from the generic varying-apex `PseudoCone` bicategory; no second notion of cone map is
introduced.

The noninvertible leg cells are available in every bicategory. Their `Iso` views require local
groupoidality, but do not require the constructor, computation, normalization, or bilimit layers.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Readable cospan-shaped cones inherit their bicategory structure from the generic
varying-apex pseudocone bicategory along `toPseudoCone`. No square-specific hom or coherence
structure is introduced. -/
instance bicategory : Bicategory (PseudoPullbackCone f g) :=
  inferInstanceAs
    (Bicategory (Bicategory.InducedBicategory
      (PseudoCone (cospan f g))
      (fun S : PseudoPullbackCone f g ↦ S.toPseudoCone)))

/-- The map between square apexes carried by a morphism of readable pseudopullback cones. -/
abbrev map {S T : PseudoPullbackCone f g} (u : S ⟶ T) : S.pt ⟶ T.pt :=
  PseudoCone.map u.hom

/-- The generic comparison modification carried by a morphism of readable pseudopullback
cones. Its boundary is the cone obtained from `T` by precomposition with `map u`, followed by
the cone represented by `S`. -/
abbrev fac {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (T.toPseudoCone.comparison S.pt).obj (PseudoPullbackCone.map u) ⟶
      S.toPseudoCone.π :=
  PseudoCone.fac u.hom

/-- The comparison cell between the first projections of a readable pseudopullback-cone
morphism. This noninvertible form is available in every ambient bicategory. -/
abbrev fstFac {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map u ≫ T.fst ⟶ S.fst :=
  PseudoCone.facApp u.hom (LocallyDiscrete.mk Limits.WalkingCospan.left)

/-- The comparison cell between the second projections of a readable pseudopullback-cone
morphism. This noninvertible form is available in every ambient bicategory. -/
abbrev sndFac {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map u ≫ T.snd ⟶ S.snd :=
  PseudoCone.facApp u.hom (LocallyDiscrete.mk Limits.WalkingCospan.right)

/-- The comparison cell at the common target of a readable pseudopullback-cone morphism.

This is the central component of the generic comparison modification. It is exposed separately
so source-facing compatibility arguments can use all three walking-cospan components without
unfolding `PseudoCone.fac`. -/
abbrev baseFac {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map u ≫ (T.fst ≫ f) ⟶ S.fst ≫ f :=
  PseudoCone.facApp u.hom (LocallyDiscrete.mk Limits.WalkingCospan.one)

/-- In a locally groupoidal ambient bicategory, the first-leg comparison of a readable
pseudopullback-cone morphism as an isomorphism. -/
noncomputable abbrev fstIso [IsLocallyGroupoid B]
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map u ≫ T.fst ≅ S.fst :=
  asIso (fstFac u)

/-- In a locally groupoidal ambient bicategory, the second-leg comparison of a readable
pseudopullback-cone morphism as an isomorphism. -/
noncomputable abbrev sndIso [IsLocallyGroupoid B]
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map u ≫ T.snd ≅ S.snd :=
  asIso (sndFac u)

/-- In a locally groupoidal ambient bicategory, the central comparison of a readable
pseudopullback-cone morphism as an isomorphism. -/
noncomputable abbrev baseIso [IsLocallyGroupoid B]
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map u ≫ (T.fst ≫ f) ≅ S.fst ≫ f :=
  asIso (baseFac u)

/-- The ambient `2`-morphism between apex maps underlying a `2`-morphism of readable
pseudopullback cones. -/
abbrev map₂ {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    PseudoPullbackCone.map u ⟶ PseudoPullbackCone.map v :=
  PseudoCone.map₂ η.hom

end Bicategory.PseudoPullbackCone

end CategoryTheory
