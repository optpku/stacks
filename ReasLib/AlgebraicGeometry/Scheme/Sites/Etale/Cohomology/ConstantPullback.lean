module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Continuous sheaf pushforward along a small-étale pullback is a right adjoint. -/
public instance instIsRightAdjoint_smallEtaleSheafPushforwardContinuous
    {Z Z' : Scheme.{u}} {p : Z' ⟶ Z} :
    ((smallEtalePullback p).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Z'.smallEtaleTopology).IsRightAdjoint :=
  sorry

/-- Sheaf pullback of abelian sheaves along a small-étale base change. -/
noncomputable abbrev etaleAbelianSheafPullback {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u} :=
  (smallEtalePullback p).sheafPullback AddCommGrpCat.{u}
    Z.smallEtaleTopology Z'.smallEtaleTopology

/-- The canonical comparison from the pullback of a constant sheaf to the constant sheaf. -/
noncomputable def constantSheaf_sheafPullback_hom
    {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) (M : AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback p).obj
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M) ⟶
    (constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M :=
  (((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Z'.smallEtaleTopology).homEquiv
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M)
      ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M)).symm
    (((sheafificationAdjunction Z.smallEtaleTopology AddCommGrpCat.{u}).homEquiv
        ((Functor.const _).obj M)
        (((smallEtalePullback p).sheafPushforwardContinuous AddCommGrpCat.{u}
            Z.smallEtaleTopology Z'.smallEtaleTopology).obj
          ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M))).symm
      ((Functor.constCompWhiskeringLeftIso (Z.Etaleᵒᵖ) (C := AddCommGrpCat.{u})
          (smallEtalePullback p).op).inv.app M ≫
        Functor.whiskerLeft (smallEtalePullback p).op
          ((sheafificationAdjunction Z'.smallEtaleTopology AddCommGrpCat.{u}).unit.app
            ((Functor.const _).obj M))))

/-- The comparison from the pullback of a constant sheaf to the constant sheaf is an isomorphism. -/
public instance isIso_constantSheaf_sheafPullback_hom
    {Z Z' : Scheme.{u}} {p : Z' ⟶ Z} {M : AddCommGrpCat.{u}} :
    IsIso (constantSheaf_sheafPullback_hom p M) :=
  sorry

/-- Sheaf pullback of a constant abelian sheaf is canonically isomorphic to the same constant sheaf. -/
noncomputable def constantSheaf_sheafPullback
    {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) (M : AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback p).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M) ≅
      (constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M :=
  asIso (constantSheaf_sheafPullback_hom p M)

/-- The pullback map on small-étale cohomology of a constant abelian sheaf. -/
noncomputable def etaleHq_constant_pullback
    {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) (M : AddCommGrpCat.{u}) (q : ℕ) :
    (Sheaf.functorH Z.smallEtaleTopology q).obj
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M) ⟶
    (Sheaf.functorH Z'.smallEtaleTopology q).obj
      ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M) :=
  AddCommGrpCat.ofHom
    ((etaleAbelianSheafPullback p).mapExtAddHom
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)))
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M) q) ≫
    AddCommGrpCat.ofHom
      (((Abelian.extFunctor q).map
          (inv (constantSheaf_sheafPullback_hom p
            (AddCommGrpCat.of (ULift ℤ)))).op).app
        ((etaleAbelianSheafPullback p).obj
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M))).hom ≫
    (Sheaf.functorH Z'.smallEtaleTopology q).map
      (constantSheaf_sheafPullback_hom p M)

end AlgebraicGeometry.Scheme.Hom
