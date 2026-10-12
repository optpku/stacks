/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.RingTheory.Henselian.StrictHenselian

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- For a strictly henselian local ring, sections on the small étale site of
the spectrum of the ring form an exact functor on abelian sheaves. -/
theorem strictHenselianGlobalSectionsExact
    {R : Type u} [CommRing R] [StrictHenselianLocalRing R] :
    exactFunctor
      (Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{u})
      AddCommGrpCat.{u}
      (siteAbelianSectionsFunctor
        (Scheme.smallEtaleTopology (Spec (.of R)))
        (MorphismProperty.Over.mk _ (𝟙 (Spec (.of R))) inferInstance)) := sorry

/-- For a sheaf of sets on the small étale site of the spectrum of a strictly
henselian local ring, sections at the identity object are isomorphic to the
stalk at the geometric point induced by the closed point. -/
theorem strictHenselianGlobalSectionsEqClosedPointStalk
    {R : Type u} [CommRing R] [StrictHenselianLocalRing R]
    (F : Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) (Type u)) :
    IsIsomorphic
      (F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of R))) inferInstance)))
      (((Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).sheafFiber).obj F) := sorry

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme

/-- A scheme whose structure-sheaf stalks are all strictly henselian local rings. -/
class HasStrictlyHenselianStalks (S : Scheme.{u}) : Prop where
  stalks : ∀ x : S, StrictHenselianLocalRing (S.presheaf.stalk x)

/-- The defining stalk condition of `HasStrictlyHenselianStalks`. -/
theorem HasStrictlyHenselianStalks.spec (S : Scheme.{u}) [HasStrictlyHenselianStalks S]
    (x : S) : StrictHenselianLocalRing (S.presheaf.stalk x) :=
  HasStrictlyHenselianStalks.stalks x

/-- The spectrum of a strictly henselian local ring has strictly henselian stalks. -/
instance instHasStrictlyHenselianStalks_of_strictHenselianLocalRing
    {R : Type u} [CommRing R] [StrictHenselianLocalRing R] :
    HasStrictlyHenselianStalks (Spec (.of R)) := sorry

/-- For a scheme with strictly henselian local rings, the cohomology of every
abelian sheaf on the small étale site is isomorphic to the cohomology of its
canonical pushforward to the small Zariski site in every degree. -/
theorem etaleCohomology_eq_zariski_of_hasStrictlyHenselianStalks
    (S : Scheme.{u}) [HasStrictlyHenselianStalks S]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (i : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify S.smallZariskiTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallZariskiTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      ((Sheaf.functorH S.smallEtaleTopology i).obj F)
      ((Sheaf.functorH S.smallZariskiTopology i).obj
        (((SiteRestriction.smallZariskiToSmallEtale S).sheafPushforwardContinuous
          AddCommGrpCat.{u} S.smallZariskiTopology S.smallEtaleTopology).obj F)) := sorry

end AlgebraicGeometry.Scheme
