/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Forward
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Reverse
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map.CospanTransform
public import stacks_project.Chap90.«90_29_1_1_Comparison»
public import stacks_project.Chap90.Remarks_90_5_2_Pushforward

/-!
# Residue-field reindexing of cofibered categories

A finite field extension `k → l` reindexes a functor `p : F ⥤ ArtinianLocalAlgCat Λ k`
along `residueChangeFunctor Λ k l` by categorical pullback. The resulting projection
`residueChangeOver p` is cofibered in groupoids whenever `p` is, and its fibre over `B`
is equivalent to the fibre of `p` over `B ×_l k`.
-/

@[expose] public section

open CategoryTheory Functor Limits
open scoped CategoricalPullback

universe u v w

namespace ArtinianLocalAlgCat

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)

noncomputable section

/-- The total category `F_{l/k}` obtained by pulling `p` back along residue-field change. -/
abbrev residueChangeTotal :=
  CategoricalPullback (residueChangeFunctor Λ k l) p

/-- The reindexed projection `p_{l/k} : F_{l/k} ⥤ C_{Λ, l}`. -/
def residueChangeOver : residueChangeTotal Λ k l p ⥤ ArtinianLocalAlgCat Λ l :=
  CategoricalPullback.π₁ (residueChangeFunctor Λ k l) p

/-- The object map of `residueChangeOver` is the first projection of the pullback triple. -/
theorem residueChangeOver_obj (ξ : residueChangeTotal Λ k l p) :
    (residueChangeOver Λ k l p).obj ξ = ξ.fst :=
  sorry

/-- The morphism map of `residueChangeOver` is the first component of a pullback morphism. -/
theorem residueChangeOver_map {ξ η : residueChangeTotal Λ k l p} (f : ξ ⟶ η) :
    (residueChangeOver Λ k l p).map f = f.fst :=
  sorry

/-- If `p` is cofibered in groupoids, then so is the residue-change reindexing `p_{l/k}`. -/
instance instIsFiberedInGroupoids_residueChangeOver [IsFibered.InGroupoids p.op] :
    IsFibered.InGroupoids (residueChangeOver Λ k l p).op :=
  sorry

namespace residueChangeOver

/-- The choice-free embedding of a fibre of `p` over `B ×_l k` into the fibre of `p_{l/k}`
over `B`. -/
def fiberMk (B : ArtinianLocalAlgCat Λ l) :
    p.Fiber ((residueChangeFunctor Λ k l).obj B) ⥤ (residueChangeOver Λ k l p).Fiber B :=
  CategoricalPullback.Fiber.reverse.functor (residueChangeFunctor Λ k l) p B

/-- Chosen pushforward of the right component of a `p_{l/k}`-fibre object along the inverse
structural isomorphism to `B ×_l k`. -/
def fiberFwdLift [IsFibered.InGroupoids p.op] {B : ArtinianLocalAlgCat Λ l}
    (X : (residueChangeOver Λ k l p).Fiber B) :
    StronglyCocartesianLift p
      (CategoricalPullback.Fiber.forward.iso (residueChangeFunctor Λ k l) p X).inv :=
  StronglyCocartesianLift.ofCleavage (cleavageOp p)
    (CategoricalPullback.Fiber.forward.iso (residueChangeFunctor Λ k l) p X).inv

/-- The chosen pushforward arrow of `fiberFwdLift` is strongly cocartesian. -/
instance instIsStronglyCocartesian_fiberFwdLift [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} (X : (residueChangeOver Λ k l p).Fiber B) :
    p.IsStronglyCocartesian
      (CategoricalPullback.Fiber.forward.iso (residueChangeFunctor Λ k l) p X).inv
      (fiberFwdLift Λ k l p X).hom :=
  (fiberFwdLift Λ k l p X).isStronglyCocartesian

/-- A vertical morphism of `p_{l/k}`-fibres, postcomposed with the chosen pushforward of its
codomain, lifts the inverse structural isomorphism of the domain. -/
instance instIsHomLift_fiberFwd_map [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} {X Y : (residueChangeOver Λ k l p).Fiber B} (φ : X ⟶ Y) :
    p.IsHomLift
      (CategoricalPullback.Fiber.forward.iso (residueChangeFunctor Λ k l) p X).inv
      (φ.1.snd ≫ (fiberFwdLift Λ k l p Y).hom) :=
  sorry

/-- The ambient arrow of `fiberFwd` on morphisms, obtained from the cocartesian universal
property of `fiberFwdLift`. -/
def fiberFwdMapHom [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} {X Y : (residueChangeOver Λ k l p).Fiber B} (φ : X ⟶ Y) :
    (fiberFwdLift Λ k l p X).target ⟶ (fiberFwdLift Λ k l p Y).target :=
  IsStronglyCocartesian.map p
    (CategoricalPullback.Fiber.forward.iso (residueChangeFunctor Λ k l) p X).inv
    (fiberFwdLift Λ k l p X).hom (Category.comp_id _).symm
    (φ.1.snd ≫ (fiberFwdLift Λ k l p Y).hom)

/-- The forward fibre comparison sending an object of `F_{l/k}` over `B` to its pushforward
in `F(B ×_l k)`. -/
def fiberFwd [IsFibered.InGroupoids p.op] (B : ArtinianLocalAlgCat Λ l) :
    (residueChangeOver Λ k l p).Fiber B ⥤ p.Fiber ((residueChangeFunctor Λ k l).obj B) where
  obj X := Fiber.mk (StronglyCocartesianLift.targetObj (fiberFwdLift Λ k l p X))
  map φ := ⟨fiberFwdMapHom Λ k l p φ, sorry⟩
  map_id := sorry
  map_comp := sorry

/-- The object map of `fiberFwd` is the target of `fiberFwdLift`. -/
theorem fiberFwd_obj [IsFibered.InGroupoids p.op] {B : ArtinianLocalAlgCat Λ l}
    (X : (residueChangeOver Λ k l p).Fiber B) :
    (fiberFwd Λ k l p B).obj X =
      Fiber.mk (StronglyCocartesianLift.targetObj (fiberFwdLift Λ k l p X)) :=
  sorry

/-- The reverse fibre embedding is an equivalence, with quasi-inverse `fiberFwd`. -/
instance fiberMk_isEquivalence [IsFibered.InGroupoids p.op] (B : ArtinianLocalAlgCat Λ l) :
    (fiberMk Λ k l p B).IsEquivalence :=
  sorry

end residueChangeOver

/-- A morphism of categories over `C_{Λ, k}` induces a morphism of residue-change reindexings. -/
def residueChangeOverMap {G : Type v} [Category.{w} G]
    (q : G ⥤ ArtinianLocalAlgCat Λ k) (φ : F ⥤ G) (hφ : φ ⋙ q = p) :
    residueChangeTotal Λ k l p ⥤ residueChangeTotal Λ k l q :=
  CategoricalPullback.map
    (CatCospanTransform.ofIso
      (rightUnitor (residueChangeFunctor Λ k l) ≪≫
        (leftUnitor (residueChangeFunctor Λ k l)).symm)
      (rightUnitor p ≪≫ eqToIso hφ.symm))

/-- Residue-change reindexing of a based morphism preserves the `C_{Λ, l}`-component. -/
theorem residueChangeOverMap_fst {G : Type v} [Category.{w} G]
    (q : G ⥤ ArtinianLocalAlgCat Λ k) (φ : F ⥤ G) (hφ : φ ⋙ q = p)
    (ξ : residueChangeTotal Λ k l p) :
    ((residueChangeOverMap Λ k l p q φ hφ).obj ξ).fst = ξ.fst :=
  sorry

end

end ArtinianLocalAlgCat
