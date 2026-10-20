module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Sites.Precoverage.CoverLifting
public import ReasLib.CategoryTheory.Sites.PrecoverageSite

/-!
# Identity-degree fiber site of a Grothendieck construction

Given `F : B ⥤ Cat` with a fiberwise precoverage, the Grothendieck construction carries the
precoverage whose covering families are identity-degree lifts of fiber coverings.
-/

@[expose] public section

universe uB vB u v

open CategoryTheory

namespace CategoryTheory.Grothendieck

variable {B : Type uB} [Category.{vB} B]

/-- A `Cat`-valued diagram whose fibers are sites and whose structure maps have selected-cover
lifts (property `P`). -/
class IsFiberwiseSite (F : B ⥤ Cat.{v, u}) (J : ∀ b, Precoverage (F.obj b)) : Prop where
  /-- Each fiber precoverage is a site. -/
  isSite : ∀ b, (J b).IsSite
  /-- Every structure map has property `P`: selected covers lift along maps from image objects. -/
  hasCoverLifts :
    ∀ {b c : B} (f : b ⟶ c),
      Functor.Precoverage.HasCoverLifts (F.map f).toFunctor (J b) (J c)

attribute [instance] IsFiberwiseSite.isSite IsFiberwiseSite.hasCoverLifts

/-- Fiberwise sites are exactly fiberwise `IsSite` together with property `P` on every structure
map. -/
theorem IsFiberwiseSite.iff (F : B ⥤ Cat.{v, u}) (J : ∀ b, Precoverage (F.obj b)) :
    IsFiberwiseSite F J ↔
      (∀ b, (J b).IsSite) ∧
        ∀ {b c : B} (f : b ⟶ c),
          Functor.Precoverage.HasCoverLifts (F.map f).toFunctor (J b) (J c) :=
  sorry

/-- A constant diagram of a site is a fiberwise site. -/
instance IsFiberwiseSite.const {C : Type u} [Category.{v} C] (J : Precoverage C) [J.IsSite] :
    IsFiberwiseSite ((Functor.const B).obj (Cat.of C)) (fun _ ↦ J) :=
  sorry

section FiberPrecoverage

variable (F : B ⥤ Cat.{v, u})

/-- The identity-degree covering family `{(id, f i)}` on an object of `Grothendieck F`. -/
def ofFiber (X : Grothendieck F) {I : Type (max u v)} (U : I → F.obj X.base)
    (f : ∀ i, U i ⟶ X.fiber) : Presieve X :=
  Presieve.ofArrows (fun i ↦ (ι F X.base).obj (U i)) (fun i ↦ (ι F X.base).map (f i))

variable (J : ∀ b, Precoverage (F.obj b))

/-- The precoverage on `Grothendieck F` whose covering families are identity-degree lifts of fiber
coverings. -/
def precoverage : Precoverage (Grothendieck F) where
  coverings X :=
    { R |
        ∃ (I : Type (max u v)) (U : I → F.obj X.base) (f : ∀ i, U i ⟶ X.fiber),
          R = ofFiber F X U f ∧ Presieve.ofArrows U f ∈ J X.base X.fiber }

/-- Membership in `precoverage F J` is an identity-degree `ofArrows` family coming from a fiber
covering. -/
theorem mem_precoverage_iff {X : Grothendieck F} {R : Presieve X} :
    R ∈ precoverage F J X ↔
      ∃ (I : Type (max u v)) (U : I → F.obj X.base) (f : ∀ i, U i ⟶ X.fiber),
        R = ofFiber F X U f ∧ Presieve.ofArrows U f ∈ J X.base X.fiber :=
  sorry

/-- An identity-degree family covers in `precoverage F J` iff the underlying fiber family covers. -/
theorem ofFiber_mem_iff {X : Grothendieck F} {I : Type (max u v)} (U : I → F.obj X.base)
    (f : ∀ i, U i ⟶ X.fiber) :
    ofFiber F X U f ∈ precoverage F J X ↔ Presieve.ofArrows U f ∈ J X.base X.fiber :=
  sorry

/-- Identity-degree fiber coverings are stable under bind. -/
instance precoverage.isStableUnderBind [IsFiberwiseSite F J] :
    (precoverage F J).IsStableUnderBind :=
  sorry

/-- Pulling back an identity-degree covering `{f i}` along `g : Y ⟶ X` yields the identity-degree
family of property-`P` fiber products in `F.obj Y.base`. Each square with legs
`(ι F Y.base).map (p i)`, the base-`g` comparison into `(ι F X.base).obj (U i)`, `g`, and
`(ι F X.base).map (f i)` is a pullback in `Grothendieck F`; this is
`W ×_{(φ, g)} U i = W ×_{g, U, f i} U i`, not `Presieve.pullbackArrows`. -/
theorem exists_ofFiber_isPullback [IsFiberwiseSite F J] {X Y : Grothendieck F} (g : Y ⟶ X)
    {I : Type (max u v)} (U : I → F.obj X.base) (f : ∀ i, U i ⟶ X.fiber)
    (hf : Presieve.ofArrows U f ∈ J X.base X.fiber) :
    ∃ (P : I → F.obj Y.base) (p : ∀ i, P i ⟶ Y.fiber)
      (q : ∀ i, (F.map g.base).toFunctor.obj (P i) ⟶ U i),
      ofFiber F Y P p ∈ precoverage F J Y ∧
        ∀ i, IsPullback ((ι F Y.base).map (p i))
          (Hom.mk g.base (q i) : (ι F Y.base).obj (P i) ⟶ (ι F X.base).obj (U i))
          g ((ι F X.base).map (f i)) :=
  sorry

/-- Covering arrows in the identity-degree fiber precoverage admit pullbacks. -/
instance precoverage.hasPullbacks [IsFiberwiseSite F J] : (precoverage F J).HasPullbacks :=
  sorry

/-- After base change, an identity-degree covering is refined by a covering that factors through
the original family. -/
instance precoverage.hasFactoringPullbacks [IsFiberwiseSite F J] :
    (precoverage F J).HasFactoringPullbacks :=
  sorry

end FiberPrecoverage

section Simplicial

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))

/-- In the simplicial case, `SimplexCategory.eq_id_of_isIso` makes every Grothendieck isomorphism
identity-degree, so it reduces to a fiber isomorphism and singleton isomorphisms cover. -/
instance precoverage.hasIsos [IsFiberwiseSite F J] : (precoverage F J).HasIsos :=
  sorry

/-- Chosen pullback families of identity-degree coverings in a simplicial
Grothendieck construction are covering families. -/
instance precoverage.isStableUnderPullbackArrows [IsFiberwiseSite F J] :
    (precoverage F J).IsStableUnderPullbackArrows := sorry

/-- The identity-degree fiber precoverage of a simplicial diagram of sites
with selected-cover lifts satisfies all site axioms. -/
instance precoverage.isSite [IsFiberwiseSite F J] : (precoverage F J).IsSite := sorry

end Simplicial

end CategoryTheory.Grothendieck
