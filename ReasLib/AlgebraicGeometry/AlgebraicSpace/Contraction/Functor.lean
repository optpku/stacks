module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Triple
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.ComplementMap
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.Objects

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization AlgebraicGeometry.Scheme.Over

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

namespace Triple

/-- Pullback of the completion component of a compatible triple is adic. -/
theorem map_isAdic {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) :
    representableByAlgebraicSpaces (completionAlong.map (ofOverMap φ) ξ.Z ≫ ξ.hatx) :=
  sorry

/-- Compatibility of an open and formal morphism is preserved by pullback. -/
theorem map_isCompatible {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) :
    IsCompatible σ V2 (ξ.Z.preimage (Points.continuous_map (ofOverMap φ)))
      (openComplementAlong.map (ofOverMap φ) ξ.Z ≫ ξ.u')
      (completionAlong.map (ofOverMap φ) ξ.Z ≫ ξ.hatx) :=
  sorry


/-- The inverse-image/restriction/completion of a triple along a morphism of
locally Noetherian schemes over `S`. -/
def map {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) : Triple σ V2 where
  Z := ξ.Z.preimage (Points.continuous_map (ofOverMap φ))
  u' := openComplementAlong.map (ofOverMap φ) ξ.Z ≫ ξ.u'
  hatx := completionAlong.map (ofOverMap φ) ξ.Z ≫ ξ.hatx
  isAdic := map_isAdic φ ξ
  isCompatible := map_isCompatible φ ξ

/-- The closed subset of `Triple.map φ ξ` is the inverse image of `ξ.Z`. -/
theorem map_Z {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) :
    (map φ ξ).Z = ξ.Z.preimage (Points.continuous_map (ofOverMap φ)) :=
  rfl

/-- The open morphism of `Triple.map φ ξ` is the restriction of `ξ.u'` along
`φ` on the open complements. -/
theorem map_u' {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) :
    (map φ ξ).u' = openComplementAlong.map (ofOverMap φ) ξ.Z ≫ ξ.u' :=
  rfl

/-- The completion morphism of `Triple.map φ ξ` is the composition of `ξ.hatx`
with the completion of `φ`. -/
theorem map_hatx {σ : ContractionSituation S} {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (ξ : Triple σ V1) :
    (map φ ξ).hatx = completionAlong.map (ofOverMap φ) ξ.Z ≫ ξ.hatx :=
  rfl

/-- Pullback of a compatible triple along the identity is unchanged. -/
theorem map_id {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (ξ : Triple σ V) :
    map (𝟙 V) ξ = ξ :=
  sorry

/-- Pullback of compatible triples respects composition of scheme morphisms. -/
theorem map_comp {σ : ContractionSituation S} {V1 V2 V3 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left]
    [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    [AlgebraicGeometry.IsLocallyNoetherian V3.left]
    (φ : V2 ⟶ V1) (ψ : V3 ⟶ V2) (ξ : Triple σ V1) :
    map (ψ ≫ φ) ξ = map ψ (map φ ξ) :=
  sorry

end Triple

/-- The contravariant functor sending a locally Noetherian scheme `V` over `S` to
the type of compatible triples `(Z, u', hatx)`, and a morphism `φ` to inverse
image, open restriction, and completion. -/
def functor (σ : ContractionSituation S) :
    (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1) where
  obj V := Triple σ V.unop.obj
  map φ := ofHom (Triple.map φ.unop.hom)
  map_id := by
    intro V
    apply ConcreteCategory.hom_ext
    intro ξ
    exact Triple.map_id ξ
  map_comp := by
    intro V1 V2 V3 φ ψ
    apply ConcreteCategory.hom_ext
    intro ξ
    exact Triple.map_comp φ.unop.hom ψ.unop.hom ξ

/-- The object map of `functor σ` is the type of triples on the underlying scheme. -/
theorem functor_obj (σ : ContractionSituation S)
    (V : (locallyNoetherian S).FullSubcategory) :
    (functor σ).obj (op V) = Triple σ V.obj :=
  rfl

/-- The morphism map of `functor σ` is `Triple.map` of the underlying arrow. -/
theorem functor_map {σ : ContractionSituation S}
    {V1 V2 : (locallyNoetherian S).FullSubcategory}
    (φ : V2 ⟶ V1) (ξ : Triple σ V1.obj) :
    (functor σ).map φ.op ξ = Triple.map φ.hom ξ :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
