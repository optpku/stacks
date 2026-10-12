/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization.Homology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of the derived internal Hom on a ringed site

The K-flat/K-injective model calculation is exposed here as a bridge from the canonical
closed-monoidal object `(ihom L).obj M` to the already reusable Hom-complex comparison API.  The
chapter presentation is therefore a recall surface and does not own a second internal-Hom model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open RingedSite.Hom
open scoped RingedSiteDerived RingedSiteCohomology RingedSiteDerivedSections

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived.InternalHom.Cohomology

variable (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}]

set_option quotPrecheck false in
local notation "D" => ModuleDerived.{z} X
set_option quotPrecheck false in
local notation "H0" => DerivedCategory.homologyFunctor AddCommGrpCat.{z} (0 : ℤ)

/-- Lemma 21.35.1 (08JA), objectwise form: degree-zero cohomology of the derived internal Hom
computes morphisms after restriction to `X/U`. -/
@[stacks 08JA "objectwise derived internal-Hom cohomology"]
theorem objectwiseH0_isomorphic_localizedHom
    [HasBinaryProducts X.carrier]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    (U : X)
    [(localizedRestriction X U).Additive]
    [PreservesFiniteLimits (localizedRestriction X U)]
    [PreservesFiniteColimits (localizedRestriction X U)]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [MonoidalCategory (ModuleDerived.{z} X)]
    [MonoidalClosed (ModuleDerived.{z} X)]
    (L M : ModuleDerived.{z} X) :
    IsIsomorphic
      (AddCommGrpCat.uliftFunctor.{max (max (max u v) w) (z + 1), z}.obj
        (H^0(U, (ihom L).obj M)))
      (AddCommGrpCat.of (((j[U]⁻¹).obj L) ⟶ ((j[U]⁻¹).obj M))) := sorry

/-- Lemma 21.35.1 (08JA), global form: global degree-zero cohomology of the derived internal Hom
computes morphisms in `D(O_X)`. -/
@[stacks 08JA "global derived internal-Hom cohomology"]
theorem globalH0_isomorphic_derivedHom
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}]
    [Functor.HasRightDerivedFunctor
      (moduleGlobalSectionsToDerived.{z} X) (ModuleQis.{z} X)]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [MonoidalCategory (ModuleDerived.{z} X)]
    [MonoidalClosed (ModuleDerived.{z} X)]
    (L M : ModuleDerived.{z} X) :
    IsIsomorphic
      (AddCommGrpCat.uliftFunctor.{max (max (max u v) w) (z + 1), z}.obj
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{z} (0 : ℤ)).obj
          ((RΓ[X]).obj ((ihom L).obj M))))
      (AddCommGrpCat.of (L ⟶ M)) := sorry

end RingedSite.Hom.ModuleDerived.InternalHom.Cohomology
