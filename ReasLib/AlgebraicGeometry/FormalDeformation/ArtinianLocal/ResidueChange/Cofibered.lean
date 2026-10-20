module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Fiber.Reverse
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Intrinsic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map.CospanTransform

/-!
# Residue-field reindexing of cofibered categories

Categorical pullback along residue-field change reindexes a cofibered groupoid
over Artinian local algebras. Its fibers are equivalent to the original fibers
over the corresponding algebra pullbacks.
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

/-- The total category obtained by pulling `p` back along residue-field change. -/
abbrev residueChangeTotal :=
  CategoricalPullback (residueChangeFunctor Λ k l) p

/-- The first projection of the categorical pullback along residue-field change. -/
def residueChangeOver : residueChangeTotal Λ k l p ⥤ ArtinianLocalAlgCat Λ l :=
  CategoricalPullback.π₁ (residueChangeFunctor Λ k l) p

/-- The object map of the reindexed projection is the first component of the pullback object. -/
theorem residueChangeOver_obj (ξ : residueChangeTotal Λ k l p) :
    (residueChangeOver Λ k l p).obj ξ = ξ.fst := sorry

/-- The morphism map of the reindexed projection is the first component of the pullback map. -/
theorem residueChangeOver_map {ξ η : residueChangeTotal Λ k l p} (φ : ξ ⟶ η) :
    (residueChangeOver Λ k l p).map φ = φ.fst := sorry

/-- Reindexing along residue-field change preserves cofiberedness in groupoids. -/
instance instIsFiberedInGroupoids_residueChangeOver [IsFibered.InGroupoids p.op] :
    IsFibered.InGroupoids (residueChangeOver Λ k l p).op := sorry

namespace residueChangeOver

/-- The choice-free embedding of the fiber of `p` over `B ×_l k` into the
fiber of its residue-change reindexing over `B`. -/
def fiberMk (B : ArtinianLocalAlgCat Λ l) :
    p.Fiber ((residueChangeFunctor Λ k l).obj B) ⥤ (residueChangeOver Λ k l p).Fiber B :=
  CategoricalPullback.Fiber.reverse.functor (residueChangeFunctor Λ k l) p B

section ForwardLift

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The structural isomorphism from the strict residue-change base point to the
image of the right component of a pullback-fiber object. -/
private def fiberBaseIso {B : ArtinianLocalAlgCat Λ l}
    (X : (residueChangeOver Λ k l p).Fiber B) :
    (residueChangeFunctor Λ k l).obj B ≅ p.obj X.1.snd :=
  eqToIso (congrArg (residueChangeFunctor Λ k l).obj X.2).symm ≪≫ X.1.iso

/-- The chosen opposite-cartesian lift of the inverse structural isomorphism;
its unopposite arrow pushes the right component forward to the strict base point. -/
def fiberFwdLift [IsFibered.InGroupoids p.op] {B : ArtinianLocalAlgCat Λ l}
    (X : (residueChangeOver Λ k l p).Fiber B) :
    StronglyCartesianLift p.op (x := Opposite.op X.1.snd)
      (fiberBaseIso Λ k l p X).inv.op :=
  StronglyCartesianLift.ofIsFibered p.op (x := Opposite.op X.1.snd)
    (fiberBaseIso Λ k l p X).inv.op

/-- The unopposite source of the chosen opposite-cartesian lift lies over `B ×_l k`. -/
theorem fiberFwdLift_targetObj [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} (X : (residueChangeOver Λ k l p).Fiber B) :
    p.obj (fiberFwdLift Λ k l p X).source.unop =
      (residueChangeFunctor Λ k l).obj B := sorry

/-- The unopposite arrow of the chosen opposite-cartesian lift is strongly cocartesian. -/
theorem fiberFwdLift_isStronglyCocartesian [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} (X : (residueChangeOver Λ k l p).Fiber B) :
    p.IsStronglyCocartesian (fiberBaseIso Λ k l p X).inv
      (fiberFwdLift Λ k l p X).hom.unop := sorry

/-- A vertical pullback-fiber arrow followed by the chosen pushforward of its codomain
lifts the inverse structural isomorphism of its domain. -/
theorem fiberFwdMap_isHomLift [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} {X Y : (residueChangeOver Λ k l p).Fiber B} (φ : X ⟶ Y) :
    p.IsHomLift (fiberBaseIso Λ k l p X).inv
      (φ.1.snd ≫ (fiberFwdLift Λ k l p Y).hom.unop) := sorry

/-- The ambient arrow between chosen pushforwards induced by the cocartesian universal property. -/
def fiberFwdMapHom [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} {X Y : (residueChangeOver Λ k l p).Fiber B} (φ : X ⟶ Y) :
    (fiberFwdLift Λ k l p X).source.unop ⟶ (fiberFwdLift Λ k l p Y).source.unop :=
  @IsStronglyCocartesian.map _ _ _ _ p _ _ _ _
    (fiberBaseIso Λ k l p X).inv (fiberFwdLift Λ k l p X).hom.unop
    (fiberFwdLift_isStronglyCocartesian Λ k l p X) _ _ (𝟙 _) _
    (Category.comp_id _).symm (φ.1.snd ≫ (fiberFwdLift Λ k l p Y).hom.unop)
    (fiberFwdMap_isHomLift Λ k l p φ)

end ForwardLift

/-- The induced arrow between chosen pushforwards is vertical over the strict base point. -/
theorem fiberFwdMapHom_isHomLift [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} {X Y : (residueChangeOver Λ k l p).Fiber B} (φ : X ⟶ Y) :
    p.IsHomLift (𝟙 ((residueChangeFunctor Λ k l).obj B))
      (fiberFwdMapHom Λ k l p φ) := sorry

/-- The fiber morphism induced by a vertical arrow between pullback-fiber objects. -/
def fiberFwdMap [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} {X Y : (residueChangeOver Λ k l p).Fiber B} (φ : X ⟶ Y) :
    Fiber.mk (fiberFwdLift_targetObj Λ k l p X) ⟶
      Fiber.mk (fiberFwdLift_targetObj Λ k l p Y) :=
  ⟨fiberFwdMapHom Λ k l p φ, fiberFwdMapHom_isHomLift Λ k l p φ⟩

/-- The forward fiber comparison preserves identity morphisms. -/
theorem fiberFwd_map_id [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} (X : (residueChangeOver Λ k l p).Fiber B) :
    fiberFwdMap Λ k l p (𝟙 X) = 𝟙 (Fiber.mk (fiberFwdLift_targetObj Λ k l p X)) := sorry

/-- The forward fiber comparison preserves composition of morphisms. -/
theorem fiberFwd_map_comp [IsFibered.InGroupoids p.op]
    {B : ArtinianLocalAlgCat Λ l} {X Y Z : (residueChangeOver Λ k l p).Fiber B}
    (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    fiberFwdMap Λ k l p (φ ≫ ψ) = fiberFwdMap Λ k l p φ ≫ fiberFwdMap Λ k l p ψ := sorry

/-- The forward fiber comparison sends a pullback-fiber object to its chosen pushforward
in the original fiber over `B ×_l k`. -/
def fiberFwd [IsFibered.InGroupoids p.op] (B : ArtinianLocalAlgCat Λ l) :
    (residueChangeOver Λ k l p).Fiber B ⥤ p.Fiber ((residueChangeFunctor Λ k l).obj B) where
  obj X := Fiber.mk (fiberFwdLift_targetObj Λ k l p X)
  map φ := fiberFwdMap Λ k l p φ
  map_id X := fiberFwd_map_id Λ k l p X
  map_comp φ ψ := fiberFwd_map_comp Λ k l p φ ψ

/-- The object map of the forward fiber comparison is the unopposite source of the
chosen opposite-cartesian lift, equipped with its base equality. -/
theorem fiberFwd_obj [IsFibered.InGroupoids p.op] {B : ArtinianLocalAlgCat Λ l}
    (X : (residueChangeOver Λ k l p).Fiber B) :
    (fiberFwd Λ k l p B).obj X =
      Fiber.mk (fiberFwdLift_targetObj Λ k l p X) := sorry

/-- The choice-free fiber embedding is an equivalence for a cofibered groupoid. -/
instance fiberMk_isEquivalence [IsFibered.InGroupoids p.op] (B : ArtinianLocalAlgCat Λ l) :
    (fiberMk Λ k l p B).IsEquivalence := sorry

end residueChangeOver

/-- A functor over the residue-field base induces a functor between the residue-change reindexings. -/
def residueChangeOverMap {G : Type v} [Category.{w} G]
    (q : G ⥤ ArtinianLocalAlgCat Λ k) (φ : F ⥤ G) (hφ : φ ⋙ q = p) :
    residueChangeTotal Λ k l p ⥤ residueChangeTotal Λ k l q :=
  CategoricalPullback.map
    (CatCospanTransform.ofIso
      (rightUnitor (residueChangeFunctor Λ k l) ≪≫
        (leftUnitor (residueChangeFunctor Λ k l)).symm)
      (rightUnitor p ≪≫ eqToIso hφ.symm))

/-- The induced functor on residue-change reindexings preserves the first object component. -/
theorem residueChangeOverMap_fst {G : Type v} [Category.{w} G]
    (q : G ⥤ ArtinianLocalAlgCat Λ k) (φ : F ⥤ G) (hφ : φ ⋙ q = p)
    (ξ : residueChangeTotal Λ k l p) :
    ((residueChangeOverMap Λ k l p q φ hφ).obj ξ).fst = ξ.fst := sorry

end

end ArtinianLocalAlgCat
