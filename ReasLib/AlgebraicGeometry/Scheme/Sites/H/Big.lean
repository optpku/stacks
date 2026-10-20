module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.CategoryTheory.Sites.Over.Topos

/-!
# Big h sheaf functors

This leaf packages the slice-site functors associated with a morphism of
schemes on the big h topology.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.H.Big

variable {S T : Scheme.{u}}

/-- The big h topology on the slice category of schemes over `S`. -/
abbrev site (S : Scheme.{u}) : GrothendieckTopology (CategoryTheory.Over S) :=
  Scheme.hPrecoverage.toGrothendieck.over S

/-- Postcomposition on the big h slice categories. -/
abbrev map (f : T ⟶ S) : CategoryTheory.Over T ⥤ CategoryTheory.Over S :=
  CategoryTheory.Over.map f

/-- Pullback on the big h slice categories. -/
abbrev pullback (f : T ⟶ S) : CategoryTheory.Over S ⥤ CategoryTheory.Over T :=
  CategoryTheory.Over.pullback f

/-- Postcomposition is continuous for the big h slice topologies. -/
def map_isContinuous (f : T ⟶ S) :
    (map f).IsContinuous (site T) (site S) := sorry

/-- Postcomposition is cocontinuous for the big h slice topologies. -/
def map_isCocontinuous (f : T ⟶ S) :
    (map f).IsCocontinuous (site T) (site S) := sorry

/-- The left Kan extensions used by the big h direct image. -/
def map_op_hasLeftKanExtension
    (f : T ⟶ S) (P : (CategoryTheory.Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasLeftKanExtension P := sorry

/-- The pointwise right Kan extensions used by the big h direct image. -/
def map_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) (P : (CategoryTheory.Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasPointwiseRightKanExtension P := sorry

/-- Weak sheafification exists for the type-valued big h slice topos. -/
def hasWeakSheafify (S : Scheme.{u}) :
    HasWeakSheafify (site S) (Type (u + 1)) := sorry

/-- The morphism of topoi induced by a scheme morphism on big h sites. -/
noncomputable def morphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn (site S) (site T) :=
  @CategoryTheory.Over.Site.morphismOfTopoi _ _ S T
    Scheme.hPrecoverage.toGrothendieck f
    (map_isContinuous f) (map_isCocontinuous f) (hasWeakSheafify S)
    (map_op_hasLeftKanExtension f) (map_op_hasPointwiseRightKanExtension f)

/-- The direct image on big h sheaves associated to a scheme morphism. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf (site T) (Type (u + 1)) ⥤ Sheaf (site S) (Type (u + 1)) :=
  (morphismOfTopoi f).pushforward

end AlgebraicGeometry.Scheme.H.Big

end

end
