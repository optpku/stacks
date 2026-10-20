/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.BivariantClass.Cospan.ProperPushforward


open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Cospan

/-- The equality used to map the left pullback of a cospan into its right pullback along a
morphism over the common middle object. -/
private theorem ofOverMorphismLift_comm
    {S : Scheme.{u}} {C E X C' Z' : Over S}
    (p : C ⟶ X) (π : E ⟶ X) (j : C ⟶ E) (hj : j ≫ π = p)
    (g : Z' ⟶ X) (iC : C' ⟶ C) (qC : C' ⟶ Z')
    (squareC : IsPullback iC.left qC.left p.left g.left) :
    (iC.left ≫ j.left) ≫ π.left = qC.left ≫ g.left := sorry

/-- The comparison into the right pullback respects the maps to the base scheme. -/
private theorem ofOverMorphismMap_over
    {S : Scheme.{u}} {C E X C' Z' E' : Over S}
    (p : C ⟶ X) (π : E ⟶ X) (j : C ⟶ E) (hj : j ≫ π = p)
    (g : Z' ⟶ X) (iC : C' ⟶ C) (qC : C' ⟶ Z')
    (squareC : IsPullback iC.left qC.left p.left g.left)
    (iE : E' ⟶ E) (qE : E' ⟶ Z')
    (squareE : IsPullback iE.left qE.left π.left g.left) :
    squareE.lift (iC.left ≫ j.left) qC.left
        (ofOverMorphismLift_comm p π j hj g iC qC squareC) ≫ E'.hom = C'.hom := sorry

/-- The canonical map between the two displayed pullbacks induced by a morphism over their
common middle object. -/
private def ofOverMorphismMap
    {S : Scheme.{u}} {C E X C' Z' E' : Over S}
    (p : C ⟶ X) (π : E ⟶ X) (j : C ⟶ E) (hj : j ≫ π = p)
    (g : Z' ⟶ X) (iC : C' ⟶ C) (qC : C' ⟶ Z')
    (squareC : IsPullback iC.left qC.left p.left g.left)
    (iE : E' ⟶ E) (qE : E' ⟶ Z')
    (squareE : IsPullback iE.left qE.left π.left g.left) : C' ⟶ E' :=
  Over.homMk
    (squareE.lift (iC.left ≫ j.left) qC.left
      (ofOverMorphismLift_comm p π j hj g iC qC squareC))
    (ofOverMorphismMap_over p π j hj g iC qC squareC iE qE squareE)

/-- The canonical comparison map forms the cartesian square required to evaluate a
bivariant class along the over-morphism. -/
private theorem ofOverMorphismMap_isPullback
    {S : Scheme.{u}} {C E X C' Z' E' : Over S}
    (p : C ⟶ X) (π : E ⟶ X) (j : C ⟶ E) (hj : j ≫ π = p)
    (g : Z' ⟶ X) (iC : C' ⟶ C) (qC : C' ⟶ Z')
    (squareC : IsPullback iC.left qC.left p.left g.left)
    (iE : E' ⟶ E) (qE : E' ⟶ Z')
    (squareE : IsPullback iE.left qE.left π.left g.left) :
    IsPullback iC.left
      (ofOverMorphismMap p π j hj g iC qC squareC iE qE squareE).left
      j.left iE.left := sorry

/-- The cospan cap family obtained from a bivariant class along a morphism over the middle
object. -/
public def ofOverMorphismCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X)
    (j : C ⟶ E) (hj : j ≫ π = p) (q : ℤ) (c : BivariantClass δ j q) :
    CapFamily δ p π q :=
  fun {_ _ _} _ _ _ g _ iC qC squareC iE _ qE squareE k ↦
    c.cap iC (ofOverMorphismMap p π j hj g iC qC squareC iE qE squareE) iE
      (ofOverMorphismMap_isPullback p π j hj g iC qC squareC iE qE squareE) k

/-- The over-morphism cap family is compatible with proper pushforward. -/
public theorem ofOverMorphismCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X)
    (j : C ⟶ E) (hj : j ≫ π = p) (q : ℤ) (c : BivariantClass δ j q) :
    CompatibleWithProperPushforward δ (ofOverMorphismCap δ p π j hj q c) := sorry

/-- The over-morphism cap family is compatible with flat pullback. -/
public theorem ofOverMorphismCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X)
    (j : C ⟶ E) (hj : j ≫ π = p) (q : ℤ) (c : BivariantClass δ j q) :
    CompatibleWithFlatPullback δ (ofOverMorphismCap δ p π j hj q c) := sorry

/-- The over-morphism cap family is compatible with effective-Cartier Gysin pullback. -/
public theorem ofOverMorphismCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X)
    (j : C ⟶ E) (hj : j ≫ π = p) (q : ℤ) (c : BivariantClass δ j q) :
    CompatibleWithCartierGysin δ (ofOverMorphismCap δ p π j hj q c) := sorry

/-- Regard a bivariant class along `j : C ⟶ E` as a cospan class on `C ⟶ X ⟵ E`
when `j` is a morphism over `X`. -/
@[expose]
public def ofOverMorphism
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X)
    (j : C ⟶ E) (hj : j ≫ π = p) (q : ℤ) (c : BivariantClass δ j q) :
    Cospan δ p π q where
  cap := ofOverMorphismCap δ p π j hj q c
  map_proper := ofOverMorphismCap_mapProper δ p π j hj q c
  pullback_flat := ofOverMorphismCap_pullbackFlat δ p π j hj q c
  gysin_cartier := ofOverMorphismCap_gysinCartier δ p π j hj q c

/-- Evaluation of `ofOverMorphism` is evaluation of the original class on the canonical
comparison of displayed pullbacks. -/
public theorem ofOverMorphism_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X Z' C' E' : Over S}
    [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z'.hom]
    [LocallyOfFiniteType C'.hom] [LocallyOfFiniteType E'.hom]
    (p : C ⟶ X) (π : E ⟶ X) (j : C ⟶ E) (hj : j ≫ π = p)
    (q : ℤ) (c : BivariantClass δ j q) (g : Z' ⟶ X)
    [LocallyOfFiniteType g.left] (iC : C' ⟶ C) (qC : C' ⟶ Z')
    (squareC : IsPullback iC.left qC.left p.left g.left)
    (iE : E' ⟶ E) [LocallyOfFiniteType iE.left] (qE : E' ⟶ Z')
    (squareE : IsPullback iE.left qE.left π.left g.left) (k : ℤ) :
    (ofOverMorphism δ p π j hj q c).cap g iC qC squareC iE qE squareE k =
      ofOverMorphismCap δ p π j hj q c g iC qC squareC iE qE squareE k := sorry

/-- Integer scaling of the cap family of a cospan bivariant class. -/
@[expose]
public def scaleCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] {p : C ⟶ X} {π : E ⟶ X} {q : ℤ}
    (n : ℤ) (c : Cospan δ p π q) : CapFamily δ p π q :=
  fun {_ _ _} _ _ _ g _ iC qC squareC iE _ qE squareE k ↦
    n • c.cap g iC qC squareC iE qE squareE k

/-- Integer scaling preserves proper-pushforward compatibility. -/
public theorem scaleCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] {p : C ⟶ X} {π : E ⟶ X} {q : ℤ}
    (n : ℤ) (c : Cospan δ p π q) :
    CompatibleWithProperPushforward δ (scaleCap δ n c) := sorry

/-- Integer scaling preserves flat-pullback compatibility. -/
public theorem scaleCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] {p : C ⟶ X} {π : E ⟶ X} {q : ℤ}
    (n : ℤ) (c : Cospan δ p π q) :
    CompatibleWithFlatPullback δ (scaleCap δ n c) := sorry

/-- Integer scaling preserves effective-Cartier Gysin compatibility. -/
public theorem scaleCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] {p : C ⟶ X} {π : E ⟶ X} {q : ℤ}
    (n : ℤ) (c : Cospan δ p π q) :
    CompatibleWithCartierGysin δ (scaleCap δ n c) := sorry

/-- Integer scaling of a cospan bivariant class. -/
@[expose]
public def scale
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] {p : C ⟶ X} {π : E ⟶ X} {q : ℤ}
    (n : ℤ) (c : Cospan δ p π q) : Cospan δ p π q where
  cap := scaleCap δ n c
  map_proper := scaleCap_mapProper δ n c
  pullback_flat := scaleCap_pullbackFlat δ n c
  gysin_cartier := scaleCap_gysinCartier δ n c

/-- Evaluation of a scaled cospan class is pointwise integer scaling. -/
public theorem scale_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X Z' C' E' : Over S}
    [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z'.hom]
    [LocallyOfFiniteType C'.hom] [LocallyOfFiniteType E'.hom]
    {p : C ⟶ X} {π : E ⟶ X} {q : ℤ} (n : ℤ) (c : Cospan δ p π q)
    (g : Z' ⟶ X) [LocallyOfFiniteType g.left]
    (iC : C' ⟶ C) (qC : C' ⟶ Z')
    (squareC : IsPullback iC.left qC.left p.left g.left)
    (iE : E' ⟶ E) [LocallyOfFiniteType iE.left] (qE : E' ⟶ Z')
    (squareE : IsPullback iE.left qE.left π.left g.left) (k : ℤ) :
    (scale δ n c).cap g iC qC squareC iE qE squareE k =
      n • c.cap g iC qC squareC iE qE squareE k := sorry

/-- The cap family obtained by applying a degree-`r` class on the right, pushing forward
along the proper right leg, and pulling back along the flat relative-dimension-`r` left leg. -/
@[expose]
public noncomputable def pushPullCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r] [IsProper π.left]
    (c : BivariantClass δ (𝟙 E) (r : ℤ)) : CapFamily δ p π 0 :=
  fun {_ C' E'} _ _ _ _ _ _ qC squareC iE _ qE squareE k ↦
    (RelativeChow.castDegree δ ((sub_add_cancel k (r : ℤ)).trans (sub_zero k).symm)).comp
      ((@ChowGroup.flatPullback S _ δ _ C' _ _ _ qC r
          (MorphismProperty.IsStableUnderBaseChange.of_isPullback squareC inferInstance)
          ((Scheme.Hom.instRelativeDimensionIsStableUnderBaseChange r).of_isPullback
            squareC inferInstance) (k - (r : ℤ))).comp
        ((@ChowGroup.map S _ δ _ E' _ _ _ qE
            (MorphismProperty.IsStableUnderBaseChange.of_isPullback squareE inferInstance)
            (k - (r : ℤ))).comp
          (c.cap iE (𝟙 E') iE IsPullback.of_id_snd k)))

/-- The push-pull cap family is compatible with proper pushforward. -/
public theorem pushPullCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r] [IsProper π.left]
    (c : BivariantClass δ (𝟙 E) (r : ℤ)) :
    CompatibleWithProperPushforward δ (pushPullCap δ p π r c) := sorry

/-- The push-pull cap family is compatible with flat pullback. -/
public theorem pushPullCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r] [IsProper π.left]
    (c : BivariantClass δ (𝟙 E) (r : ℤ)) :
    CompatibleWithFlatPullback δ (pushPullCap δ p π r c) := sorry

/-- The push-pull cap family is compatible with effective-Cartier Gysin pullback. -/
public theorem pushPullCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r] [IsProper π.left]
    (c : BivariantClass δ (𝟙 E) (r : ℤ)) :
    CompatibleWithCartierGysin δ (pushPullCap δ p π r c) := sorry

/-- The degree-zero cospan class `p^* ∘ π_* ∘ c` for a degree-`r` class `c`, a proper
right leg `π`, and a flat relative-dimension-`r` left leg `p`. -/
@[expose]
public noncomputable def pushPull
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r] [IsProper π.left]
    (c : BivariantClass δ (𝟙 E) (r : ℤ)) : Cospan δ p π 0 where
  cap := pushPullCap δ p π r c
  map_proper := pushPullCap_mapProper δ p π r c
  pullback_flat := pushPullCap_pullbackFlat δ p π r c
  gysin_cartier := pushPullCap_gysinCartier δ p π r c

/-- Evaluation of `pushPull` is its explicit Chern-cap, proper-pushforward, flat-pullback
cap family. -/
public theorem pushPull_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {C E X : Over S} [LocallyOfFiniteType C.hom] [LocallyOfFiniteType E.hom]
    [LocallyOfFiniteType X.hom] (p : C ⟶ X) (π : E ⟶ X) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r] [IsProper π.left]
    (c : BivariantClass δ (𝟙 E) (r : ℤ)) :
    ((pushPull δ p π r c).cap : CapFamily δ p π 0) =
      (pushPullCap δ p π r c : CapFamily δ p π 0) := sorry

end AlgebraicGeometry.BivariantClass.Cospan
