module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.RingTheory.Henselian
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Leray
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Over a henselian local ring, the restriction of an injective sheaf of modules over
constant prime-order coefficients on the projective line to its closed fibre has
vanishing étale cohomology in every positive degree. -/
theorem etaleCohomology_restrict_injective_eq_zero_of_projectiveLine_henselian
    {A : Type u} [CommRing A] [HenselianLocalRing A] (ℓ : ℕ) [Fact ℓ.Prime]
    [HasSheafify (ProjectiveSpace 1 (Spec (CommRingCat.of A))).smallEtaleTopology RingCat.{u}]
    [HasSheafify (ProjectiveSpace 1 (Spec (CommRingCat.of A))).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (ProjectiveSpace 1 (Spec (CommRingCat.of A))).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (ProjectiveSpace 1 (Spec (CommRingCat.of A))).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (ProjectiveSpace 1 (Spec (CommRingCat.of A))).Etale]
    [(siteAbelianSectionsFunctor (ProjectiveSpace 1 (Spec (CommRingCat.of A))).smallEtaleTopology
        (terminal (ProjectiveSpace 1 (Spec (CommRingCat.of A))).Etale)).Additive]
    [HasSheafify ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber (IsLocalRing.closedPoint A)).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber (IsLocalRing.closedPoint A)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber (IsLocalRing.closedPoint A)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber (IsLocalRing.closedPoint A)).Etale]
    [(siteAbelianSectionsFunctor ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber (IsLocalRing.closedPoint A)).smallEtaleTopology
        (terminal ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber (IsLocalRing.closedPoint A)).Etale)).Additive]
    [((smallEtalePullback ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiberι (IsLocalRing.closedPoint A))).sheafPushforwardContinuous
        AddCommGrpCat.{u} (ProjectiveSpace 1 (Spec (CommRingCat.of A))).smallEtaleTopology
        ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber (IsLocalRing.closedPoint A)).smallEtaleTopology).IsRightAdjoint]
    (I : SheafOfModules
      ((constantSheaf (ProjectiveSpace 1 (Spec (CommRingCat.of A))).smallEtaleTopology RingCat.{u}).obj
        (.of (ULift.{u} (ZMod ℓ)))))
    [Injective I] {q : ℕ} (hq : 0 < q) :
    IsZero (etaleCohomology ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber (IsLocalRing.closedPoint A))
      ((etaleAbelianRestriction ((ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiberι (IsLocalRing.closedPoint A))).obj
        ((SheafOfModules.toSheaf _).obj I)) q) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
