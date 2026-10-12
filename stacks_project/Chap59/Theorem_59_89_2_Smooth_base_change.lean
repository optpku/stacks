/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import stacks_project.Chap59.Lemma_59_29_7
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Geometric stalk of an abelian sheaf on the small étale site, as the sheaf
fiber of the associated small-étale point. -/
noncomputable abbrev abelianGeometricStalk {T : Scheme.{u}}
    (t : GeometricPoint T) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.{u} :=
  (GeometricPoint.toSmallEtalePoint t).sheafFiber.obj F

/-- `abelianGeometricStalk` is the sheaf fiber of `toSmallEtalePoint`. -/
theorem abelianGeometricStalk_eq {T : Scheme.{u}} (t : GeometricPoint T)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) :
    abelianGeometricStalk t F =
      (GeometricPoint.toSmallEtalePoint t).sheafFiber.obj F := sorry

/-- An abelian sheaf on the small étale site of `T` has geometric stalks that are
torsion of orders invertible on `S` if every element of every geometric stalk is
annihilated by some nonzero `n : ℕ` which is a unit in `Γ(S, ⊤)`. -/
def IsTorsionWithOrdersInvertibleOn {T : Scheme.{u}} (S : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  ∀ (t : GeometricPoint T) (a : abelianGeometricStalk t F),
    ∃ n : ℕ, n ≠ 0 ∧ n • a = 0 ∧ IsUnit (n : Γ(S, ⊤))

/-- Unfold `IsTorsionWithOrdersInvertibleOn` into the stalkwise annihilator and
invertibility condition. -/
theorem isTorsionWithOrdersInvertibleOn_iff {T : Scheme.{u}} (S : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) :
    IsTorsionWithOrdersInvertibleOn S F ↔
      ∀ (t : GeometricPoint T) (a : abelianGeometricStalk t F),
        ∃ n : ℕ, n ≠ 0 ∧ n • a = 0 ∧ IsUnit (n : Γ(S, ⊤)) := sorry

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Theorem 59.89.2 (Smooth base change): for a cartesian square of schemes with
legs `h : Y ⟶ X`, `e : Y ⟶ T`, `f : X ⟶ S` and `g : T ⟶ S`, if `f` is smooth and
`g` is quasi-compact and quasi-separated, then `f⁻¹ R^q g_* F ≅ R^q h_* e⁻¹ F`
for every `q` and every abelian sheaf `F` on `T` with the small étale topology
whose geometric stalks are torsion of orders invertible on `S`. The comparison
is the derived mate `higherDirectImage_baseChangeHom g f h e h_cart.flip F q`. -/
@[stacks 0EYU]
theorem higherDirectImage_baseChangeHom_isIso_of_smooth
    {X S T Y : Scheme.{u}} (f : X ⟶ S) [Smooth f] (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] (h : Y ⟶ X) (e : Y ⟶ T)
    (h_cart : IsPullback h e f g)
    {F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}}
    (hF : IsTorsionWithOrdersInvertibleOn S F) (q : ℕ) :
    IsIso (higherDirectImage_baseChangeHom g f h e h_cart.flip F q) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
