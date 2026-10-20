/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

/-- Every fppf covering sieve on `Over S` is covering for the big ph topology. -/
theorem fppf_le_ph (S : Scheme.{u}) :
    Scheme.fppfTopology.over S ≤ Scheme.bigPhSite S := sorry

/-- The identity on `Over S` is the site functor from the big fppf site to the
big ph site. -/
instance identity_isMorphismOfSites (S : Scheme.{u}) :
    IsMorphismOfSites (Scheme.fppfTopology.over S) (Scheme.bigPhSite S)
      (𝟭 (Over S)) := sorry

/-- Pullback along the identity from fppf sheaves to ph sheaves preserves
finite limits. -/
instance identitySheafPullback_preservesFiniteLimits (S : Scheme.{u}) :
    Limits.PreservesFiniteLimits
      ((𝟭 (Over S)).sheafPullback (Type (u + 1))
        (Scheme.fppfTopology.over S) (Scheme.bigPhSite S)) := sorry

/-- Ph sheafification of the underlying presheaf of an fppf sheaf. -/
def sheafification (S : Scheme.{u}) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) ⥤
      Sheaf (Scheme.bigPhSite S) (Type (u + 1)) :=
  sheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1)) ⋙
    presheafToSheaf (Scheme.bigPhSite S) (Type (u + 1))

/-- Ph sheafification is left adjoint to restriction along the identity site functor. -/
def sheafificationAdjunction (S : Scheme.{u}) :
    sheafification S ⊣
      (𝟭 (Over S)).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.fppfTopology.over S) (Scheme.bigPhSite S) :=
  (CategoryTheory.sheafificationAdjunction
      (Scheme.bigPhSite S) (Type (u + 1))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- The morphism of topoi from the big ph site to the big fppf site over `S`. -/
def epsilon (S : Scheme.{u}) :
    MorphismOfTopoiIn (Scheme.fppfTopology.over S) (Scheme.bigPhSite S) :=
  (IsMorphismOfSites.toMorphismOfTopoiIn (𝟭 (Over S)) :
    LeftExactAdjunction
      (Sheaf (Scheme.bigPhSite S) (Type (u + 1)))
      (Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))))

/-- The direct image of `epsilon S` is restriction along the identity site functor. -/
theorem epsilon_pushforward (S : Scheme.{u}) :
    (epsilon S).pushforward =
      (𝟭 (Over S)).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.fppfTopology.over S) (Scheme.bigPhSite S) := sorry

/-- The direct image of `epsilon S` leaves the entire underlying presheaf unchanged. -/
theorem epsilon_pushforward_val (S : Scheme.{u})
    (F : Sheaf (Scheme.bigPhSite S) (Type (u + 1))) :
    ((epsilon S).pushforward.obj F).obj = F.obj := sorry

/-- The inverse image of `epsilon S` is canonically ph sheafification. -/
def epsilonInverseImageIsoSheafification (S : Scheme.{u}) :
    (epsilon S).inverseImage ≅ sheafification S :=
  Adjunction.leftAdjointUniq
    ((𝟭 (Over S)).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.fppfTopology.over S) (Scheme.bigPhSite S))
    (sheafificationAdjunction S)

/-- The comparison from the big ph site to a standard site, obtained through fppf. -/
def standardComparison (τ : StandardTopology) (S : Scheme.{u}) :
    MorphismOfTopoiIn (τ.overTopology S) (Scheme.bigPhSite S) :=
  MorphismOfTopoiIn.comp (StandardTopology.toFppf τ S) (epsilon S)

/-- At the fppf member, `standardComparison` is the ph-to-fppf comparison. -/
theorem standardComparison_fppf (S : Scheme.{u}) :
    standardComparison .fppf S = epsilon S := sorry

end AlgebraicGeometry.Scheme.PhComparison
