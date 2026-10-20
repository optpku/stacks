module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.CategoryTheory.Sites.TopologyComparison
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Over.Topos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityRelocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Site

/-!
# Comparison of ph and étale topoi

The identity on a big slice site induces the comparison from ph to étale
sheaves. Composing with identity-base étale relocalization gives the comparison
to the small étale topos. Both comparisons commute with morphisms of algebraic
spaces.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The big étale slice topology is coarser than the big ph slice topology. -/
theorem overEtaleTopology_le_bigPhSite (X : AlgebraicSpace S) :
    overEtaleTopology X ≤ bigPhSite X := sorry

/-- The identity on `Over X` is continuous from `(Spaces/X)_étale` to
`(Spaces/X)_ph`. -/
instance identity_etale_isContinuous_ph (X : AlgebraicSpace S) :
    Functor.IsContinuous (𝟭 (Over X)) (overEtaleTopology X) (bigPhSite X) :=
  Functor.id_isContinuous_of_le (overEtaleTopology_le_bigPhSite X)

/-- The opposite identity functor admits left Kan extensions of type-valued
presheaves. -/
instance identity_op_hasLeftKanExtension (X : AlgebraicSpace S)
    (P : (Over X)ᵒᵖ ⥤ Type (u + 1)) :
    (𝟭 (Over X)).op.HasLeftKanExtension P :=
  Functor.HasLeftKanExtension.mk P P.leftUnitor.inv

/-- Sheaf pullback along the identity from the étale slice topology to the ph
slice topology preserves finite limits. -/
instance identity_etale_ph_sheafPullback_preservesFiniteLimits (X : AlgebraicSpace S) :
    PreservesFiniteLimits
      ((𝟭 (Over X)).sheafPullback (Type (u + 1))
        (overEtaleTopology X) (bigPhSite X)) := sorry

namespace PhComparison

/-- The comparison morphism of topoi `ε_X : Sh((Spaces/X)_ph) ⟶ Sh((Spaces/X)_étale)`
induced by the identity site functor. -/
def epsilon (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (overEtaleTopology X) (bigPhSite X) :=
  (𝟭 (Over X)).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (overEtaleTopology X) (bigPhSite X)

/-- `epsilon X` is the topos morphism of the identity site functor from
`(Spaces/X)_étale` to `(Spaces/X)_ph`. -/
theorem epsilon_eq (X : AlgebraicSpace S) :
    epsilon X =
      (𝟭 (Over X)).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
        (overEtaleTopology X) (bigPhSite X) :=
  rfl

/-- The inverse-image projection of `epsilon`. -/
@[simp]
theorem epsilon_inverseImage (X : AlgebraicSpace S) :
    (epsilon X)⁻¹ =
      (𝟭 (Over X)).sheafPullback (Type (u + 1))
        (overEtaleTopology X) (bigPhSite X) :=
  rfl

/-- The direct-image projection of `epsilon`. -/
@[simp]
theorem epsilon_pushforward (X : AlgebraicSpace S) :
    (epsilon X).pushforward =
      (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
        (overEtaleTopology X) (bigPhSite X) :=
  rfl

/-- The composite comparison `a_X = π_X ∘ ε_X` from the big ph topos to the
small étale topos. -/
def toSmallEtale (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (bigPhSite X) :=
  MorphismOfTopoiIn.comp (Etale.SmallToBig.siteMorphismOfTopoi X) (epsilon X)

/-- The comparison to the small étale topos is the composite of the
big ph-to-étale and big-to-small étale comparisons. -/
theorem toSmallEtale_eq_comp (X : AlgebraicSpace S) :
    toSmallEtale X =
      MorphismOfTopoiIn.comp (Etale.SmallToBig.siteMorphismOfTopoi X) (epsilon X) :=
  rfl

variable {X Y : AlgebraicSpace S}

/-- Direct image along `f_big,ph` and `f_big,étale` form a commutative square
with the identity comparisons `ε_X` and `ε_Y`. -/
theorem bigPhEtaleCommSq (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f).pushforward
      (epsilon X).pushforward
      (epsilon Y).pushforward
      (Etale.Big.morphismOfTopoi f).pushforward) :=
  sorry

/-- Direct image along `f_big,ph` and `f_small` form a commutative square with
`a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`. -/
theorem phSmallEtaleCommSq (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f).pushforward
      (toSmallEtale X).pushforward
      (toSmallEtale Y).pushforward
      (smallEtaleMorphismOfTopoi f).pushforward) :=
  sorry

end PhComparison

end AlgebraicGeometry.AlgebraicSpace

end

end
