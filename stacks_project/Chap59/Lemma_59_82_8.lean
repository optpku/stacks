module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import stacks_project.Chap59.Lemma_59_82_1
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 59.82.8: if a scheme `X` has affine diagonal and is covered by `n + 1`
affine opens, `Z` is a closed subscheme of `X`, `A` is a torsion sheaf of rings
on `X_étale`, and `I` is an injective sheaf of `A`-modules, then étale cohomology
of the restriction of `I` to `Z` vanishes in degrees `q` with `n < q`. -/
@[stacks 0A51]
theorem etaleCohomology_restrict_injective_eq_zero_of_affineCover
    {X Z : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (n : ℕ) (U : Fin (n + 1) → X.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : ⨆ j, U j = ⊤)
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X.Etale]
    [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal Z.Etale]
    [(siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive]
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint]
    (A : Sheaf X.smallEtaleTopology RingCat.{u})
    (hA : Sheaf.IsLocallyTorsion
      ((sheafCompose X.smallEtaleTopology
          (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj A))
    (I : SheafOfModules A) [Injective I] {q : ℕ} (hq : n < q) :
    IsZero (etaleCohomology Z
      ((etaleAbelianRestriction i).obj ((SheafOfModules.toSheaf A).obj I)) q) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
