module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap59.Proposition_59_55_2_Over
public import stacks_project.Chap63.Lemma_63_4_5
public import stacks_project.Chap63.Lemma_63_4_12_Comparison

/-!
# Stalk reindexing for locally quasi-finite lower-shriek composition

Geometric points of `X` over `z̄` via `g ∘ f` are pairs of a point of `Y`
over `z̄` and a point of `X` over that point. This reindexes the coproduct
formula of Lemma 63.4.5 for `(g ∘ f)_!`.
-/

@[expose] public section

open CategoryTheory hiding Over
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (zbar : GeometricPoint Z)

/-- Same-field geometric points of `X` over `zbar` via `f ≫ g` correspond to a
point of `Y` over `zbar` together with a point of `X` over that point. -/
def Over.compEquiv :
    Over (f ≫ g) zbar ≃ (y : Over g zbar) × Over f y.toGeometricPoint where
  toFun x :=
    let y := Over.of g zbar (x.toScheme ≫ f)
      (Eq.trans (Category.assoc x.toScheme f g) x.fac)
    ⟨y, Over.of f y.toGeometricPoint x.toScheme rfl⟩
  invFun p :=
    Over.of (f ≫ g) zbar p.2.toScheme
      (Eq.trans (Eq.trans (Eq.symm (Category.assoc p.2.toScheme f g))
            (congrArg (fun t ↦ t ≫ g) p.2.fac))
        (Eq.trans (congrArg (fun t ↦ t ≫ g) p.1.toGeometricPoint_hom) p.1.fac))
  left_inv := sorry
  right_inv := sorry

/-- The first factor of `Over.compEquiv` is composition with `f`. -/
theorem Over.compEquiv_fst (x : Over (f ≫ g) zbar) :
    (Over.compEquiv f g zbar x).1.toScheme = x.toScheme ≫ f :=
  sorry

/-- The second factor of `Over.compEquiv` recovers the morphism to `X`. -/
theorem Over.compEquiv_snd (x : Over (f ≫ g) zbar) :
    (Over.compEquiv f g zbar x).2.toScheme = x.toScheme :=
  sorry

/-- The geometric point of `X` is unchanged by `Over.compEquiv`. -/
theorem Over.compEquiv_toGeometricPoint (x : Over (f ≫ g) zbar) :
    (Over.compEquiv f g zbar x).2.toGeometricPoint = x.toGeometricPoint :=
  sorry

end AlgebraicGeometry.Scheme.GeometricPoint

namespace AlgebraicGeometry.Scheme.Etale

open AlgebraicGeometry.Scheme.GeometricPoint

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable (zbar : GeometricPoint Z)

/-- Reindexing of fibrewise stalk coproducts along `Over.compEquiv`, using the
stalk formula of Lemma 63.4.5 on `f`. -/
def abelianStalkCoproductCompIso :
    lowerShriek f ⋙ abelianStalkCoproduct g zbar ≅
      abelianStalkCoproduct (f ≫ g) zbar :=
  NatIso.ofComponents
    (fun F ↦
      { hom :=
          Sigma.desc fun y : Over g zbar ↦
            ((lowerShriekStalkIso f y.toGeometricPoint).app F).hom ≫
              Sigma.desc fun x : Over f y.toGeometricPoint ↦
                Sigma.ι
                  (fun w : Over (f ≫ g) zbar ↦
                    (toSmallEtalePoint w.toGeometricPoint).sheafFiber.obj F)
                  ((Over.compEquiv f g zbar).symm ⟨y, x⟩)
        inv :=
          Sigma.desc fun w : Over (f ≫ g) zbar ↦
            Sigma.ι
                (fun x : Over f (Over.compEquiv f g zbar w).1.toGeometricPoint ↦
                  (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F)
                (Over.compEquiv f g zbar w).2 ≫
              ((lowerShriekStalkIso f
                  (Over.compEquiv f g zbar w).1.toGeometricPoint).app F).inv ≫
                Sigma.ι
                  (fun y : Over g zbar ↦
                    (toSmallEtalePoint y.toGeometricPoint).sheafFiber.obj
                      ((lowerShriek f).obj F))
                  (Over.compEquiv f g zbar w).1
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The forward map of `abelianStalkCoproductCompIso` is the coproduct of stalk
identifications of `f`, reindexed by `Over.compEquiv`. -/
theorem abelianStalkCoproductCompIso_hom
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproductCompIso f g zbar).hom.app F =
      Sigma.desc fun y : Over g zbar ↦
        ((lowerShriekStalkIso f y.toGeometricPoint).app F).hom ≫
          Sigma.desc fun x : Over f y.toGeometricPoint ↦
            Sigma.ι
              (fun w : Over (f ≫ g) zbar ↦
                (toSmallEtalePoint w.toGeometricPoint).sheafFiber.obj F)
              ((Over.compEquiv f g zbar).symm ⟨y, x⟩) :=
  sorry

/-- Inner path of the stalk square: the stalk formula of Lemma 63.4.5 for
`f ≫ g`. -/
def lowerShriekFunctorCompIso_stalk_inner
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint zbar).sheafFiber.obj ((lowerShriek (f ≫ g)).obj F) ⟶
      (abelianStalkCoproduct (f ≫ g) zbar).obj F :=
  ((lowerShriekStalkIso (f ≫ g) zbar).app F).hom

/-- Outer path of the stalk square: the stalk formula of `g` at `f_! F`, then
reindexing of the stalk formula of `f`. -/
def lowerShriekFunctorCompIso_stalk_outer
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint zbar).sheafFiber.obj
        ((lowerShriek g).obj ((lowerShriek f).obj F)) ⟶
      (abelianStalkCoproduct (f ≫ g) zbar).obj F :=
  ((lowerShriekStalkIso g zbar).app ((lowerShriek f).obj F)).hom ≫
    (abelianStalkCoproductCompIso f g zbar).hom.app F

end AlgebraicGeometry.Scheme.Etale

end
