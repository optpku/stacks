module

public import stacks_project.Chap98.Lemma_98_25_2_Noetherian
public import stacks_project.Chap98.Lemma_98_27_4_Triple

/-!
# The contraction functor

The rule `F` sending a locally Noetherian scheme `V` over `S` to the type of
compatible triples, and a morphism `φ : V2 ⟶ V1` to inverse image of the closed
subset, restriction of the open morphism, and completion of `φ`, is a
contravariant functor on `(locallyNoetherian S).FullSubcategory`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty Opposite
open TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over

/-- An object of `locallyNoetherian S` is a locally Noetherian scheme over `S`. -/
instance instIsLocallyNoetherian_locallyNoetherianObj {S : Scheme.{u}}
    (V : (locallyNoetherian S).FullSubcategory) :
    AlgebraicGeometry.IsLocallyNoetherian V.obj.left :=
  V.property

end AlgebraicGeometry.Scheme.Over

namespace AlgebraicGeometry.AlgebraicSpace

namespace openComplementAlong

/-- Membership of a Yoneda section in the open complement of `T` is stable under
postcomposition with `f : X' ⟶ X`. -/
theorem mapsInto_comp {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) {U : (Over S)ᵒᵖ} {x : X'.functorOfPoints.obj U}
    (hx : Set.range (Points.map (OpenSubspace.homOfPointsSection x)) ⊆
      (openComplement X' (T.preimage (Points.continuous_map f)) : Set (Points X'))) :
    Set.range (Points.map (OpenSubspace.homOfPointsSection (f.app U x))) ⊆
      (openComplement X T : Set (Points X)) :=
  sorry

/-- The morphism of open complements induced by `f : X' ⟶ X`, landing in the
closed preimage `T.preimage (Points.continuous_map f)`. -/
def map {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    openComplementAlong X' (T.preimage (Points.continuous_map f)) ⟶
      openComplementAlong X T where
  app U := ofHom fun x ↦ ⟨f.app U x.1, mapsInto_comp f T x.2⟩
  naturality := sorry

/-- The underlying section of `map f T` is the component of `f`. -/
theorem map_app {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (x : (openComplementAlong X' (T.preimage (Points.continuous_map f))).functorOfPoints.obj U) :
    (openComplementι X T).app U ((map f T).app U x) =
      f.app U ((openComplementι X' (T.preimage (Points.continuous_map f))).app U x) :=
  sorry

end openComplementAlong

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

namespace Triple

/-- The inverse-image/restriction/completion of a triple along a morphism of
locally Noetherian schemes over `S`. -/
def map {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) : Triple σ V2 where
  Z := ξ.Z.preimage (Points.continuous_map (ofOverMap φ))
  u' := openComplementAlong.map (ofOverMap φ) ξ.Z ≫ ξ.u'
  hatx := completionAlong.map (ofOverMap φ) ξ.Z ≫ ξ.hatx
  isAdic := sorry
  isCompatible := sorry

/-- The closed subset of `Triple.map φ ξ` is the inverse image of `ξ.Z`. -/
theorem map_Z {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) :
    (map φ ξ).Z = ξ.Z.preimage (Points.continuous_map (ofOverMap φ)) :=
  sorry

/-- The open morphism of `Triple.map φ ξ` is the restriction of `ξ.u'` along
`φ` on the open complements. -/
theorem map_u' {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) :
    (map φ ξ).u' = openComplementAlong.map (ofOverMap φ) ξ.Z ≫ ξ.u' :=
  sorry

/-- The completion morphism of `Triple.map φ ξ` is the composition of `ξ.hatx`
with the completion of `φ`. -/
theorem map_hatx {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) :
    (map φ ξ).hatx = completionAlong.map (ofOverMap φ) ξ.Z ≫ ξ.hatx :=
  sorry

end Triple

/-- The contravariant functor sending a locally Noetherian scheme `V` over `S` to
the type of compatible triples `(Z, u', hatx)`, and a morphism `φ` to inverse
image, open restriction, and completion. -/
def functor (σ : ContractionSituation S) :
    (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1) where
  obj V := Triple σ V.unop.obj
  map φ := ofHom (Triple.map φ.unop.hom)
  map_id := sorry
  map_comp := sorry

/-- The object map of `functor σ` is the type of triples on the underlying scheme. -/
theorem functor_obj (σ : ContractionSituation S)
    (V : (locallyNoetherian S).FullSubcategory) :
    (functor σ).obj (op V) = Triple σ V.obj :=
  sorry

/-- The morphism map of `functor σ` is `Triple.map` of the underlying arrow. -/
theorem functor_map {σ : ContractionSituation S}
    {V1 V2 : (locallyNoetherian S).FullSubcategory}
    (φ : V2 ⟶ V1) (ξ : Triple σ V1.obj) :
    (functor σ).map φ.op ξ = Triple.map φ.hom ξ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
