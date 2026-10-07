module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.DeltaOne.Endpoint
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Homotopy
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Projection
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Homotopy

/-!
@stack 019O

# Contractions of the simplicial-interval copower

This module relates the cylinder endpoints to the canonical copower projection and lifts the
maximum and minimum homotopies of `Δ[1]` to contractions of the simplicial cylinder.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.copower.deltaOne

variable {C : Type u} [Category.{v} C]
variable (X : SimplicialObject C)
variable [HasCopower (Δ[1] : SSet.{w}) X]

/-- Every endpoint is a section of the canonical projection from the simplicial cylinder. -/
@[reassoc, stacks 019O "endpoint splits the simplicial cylinder projection"]
theorem endpoint.comp_projection (i : Fin 2) :
    endpoint X i ≫ copower.projection X (Δ[1] : SSet.{w}) = 𝟙 X := sorry

/-- The canonical split-mono structure on a simplicial-cylinder endpoint, retracted by the
cylinder projection. -/
@[stacks 019O "canonical split-mono structure on a simplicial cylinder endpoint"]
def endpoint.splitMono (i : Fin 2) : SplitMono (endpoint X i) where
  retraction := copower.projection X (Δ[1] : SSet.{w})
  id := endpoint.comp_projection X i

/-- Simplicial-cylinder endpoints are canonically split monomorphisms. -/
@[stacks 019O "simplicial cylinder endpoints are split monomorphisms"]
instance endpoint.isSplitMono (i : Fin 2) : IsSplitMono (endpoint X i) :=
  IsSplitMono.mk' (endpoint.splitMono X i)

/-- The cylinder projection has the zero endpoint as its canonical section. -/
@[stacks 019O "canonical split-epi structure on the simplicial cylinder projection"]
def projection.splitEpi :
    SplitEpi (copower.projection X (Δ[1] : SSet.{w})) where
  section_ := endpointZero X
  id := endpoint.comp_projection X (0 : Fin 2)

/-- The simplicial-cylinder projection is canonically a split epimorphism. -/
@[stacks 019O "simplicial cylinder projection is a split epimorphism"]
instance projection.isSplitEpi :
    IsSplitEpi (copower.projection X (Δ[1] : SSet.{w})) :=
  IsSplitEpi.mk' (projection.splitEpi X)

/-- Lemma 14.26.8 (1): the zero endpoint is a section of the cylinder projection. -/
@[reassoc, stacks 019O "zero endpoint splits the simplicial cylinder projection"]
theorem endpointZero.comp_projection :
    endpointZero X ≫ copower.projection X (Δ[1] : SSet.{w}) = 𝟙 X := sorry

/-- Lemma 14.26.8 (1): the one endpoint is a section of the cylinder projection. -/
@[reassoc, stacks 019O "one endpoint splits the simplicial cylinder projection"]
theorem endpointOne.comp_projection :
    endpointOne X ≫ copower.projection X (Δ[1] : SSet.{w}) = 𝟙 X := sorry

/-- Projection followed by an endpoint is reindexing along the corresponding constant
endomorphism of `Δ[1]`. -/
@[stacks 019O "simplicial cylinder projection-endpoint composite"]
theorem endpoint.projection_comp (i : Fin 2) :
    copower.projection X (Δ[1] : SSet.{w}) ≫ endpoint X i =
      copower.indexHom X (SSet.deltaOne.const i) := sorry

/-- Projection followed by the zero endpoint is reindexing along the constant-zero map. -/
@[stacks 019O "zero endpoint after the simplicial cylinder projection"]
theorem endpointZero.projection_comp :
    copower.projection X (Δ[1] : SSet.{w}) ≫ endpointZero X =
      copower.indexHom X (SSet.deltaOne.const (0 : Fin 2)) := sorry

/-- Projection followed by the one endpoint is reindexing along the constant-one map. -/
@[stacks 019O "one endpoint after the simplicial cylinder projection"]
theorem endpointOne.projection_comp :
    copower.projection X (Δ[1] : SSet.{w}) ≫ endpointOne X =
      copower.indexHom X (SSet.deltaOne.const (1 : Fin 2)) := sorry

/-- The pointwise-maximum homotopy lifted through copower reindexing. -/
@[stacks 019O "maximum homotopy on a simplicial copower cylinder"]
noncomputable def max.homotopy :
    SimplicialObject.Homotopy
      (copower.indexHom X (𝟙 (Δ[1] : SSet.{w})))
      (copower.indexHom X (SSet.deltaOne.const (1 : Fin 2))) :=
  copower.indexHom.homotopy X SSet.deltaOne.max.homotopy

/-- The maximum contraction, expressed with the canonical cylinder projection and one endpoint.
This is the direction from the identity to the endpoint composite. -/
@[stacks 019O "one-endpoint concrete cylinder homotopy"]
noncomputable def endpointOne.homotopy :
    SimplicialObject.Homotopy
      (𝟙 (SimplicialObject.copower (Δ[1] : SSet.{w}) X))
      (copower.projection X (Δ[1] : SSet.{w}) ≫ endpointOne X) :=
  SimplicialObject.Homotopy.cast
    (copower.indexHom.id X (Δ[1] : SSet.{w}))
    (endpointOne.projection_comp X).symm
    (max.homotopy X)

/-- The pointwise-minimum homotopy lifted through copower reindexing. -/
@[stacks 019O "minimum homotopy on a simplicial copower cylinder"]
noncomputable def min.homotopy :
    SimplicialObject.Homotopy
      (copower.indexHom X (SSet.deltaOne.const (0 : Fin 2)))
      (copower.indexHom X (𝟙 (Δ[1] : SSet.{w}))) :=
  copower.indexHom.homotopy X SSet.deltaOne.min.homotopy

/-- The minimum contraction, expressed with the canonical cylinder projection and zero endpoint.
This is the direction used by a section of the projection: the composite contracts to the
identity. -/
@[stacks 019O "zero-endpoint concrete cylinder homotopy"]
noncomputable def endpointZero.homotopy :
    SimplicialObject.Homotopy
      (copower.projection X (Δ[1] : SSet.{w}) ≫ endpointZero X)
      (𝟙 (SimplicialObject.copower (Δ[1] : SSet.{w}) X)) :=
  SimplicialObject.Homotopy.cast
    (endpointZero.projection_comp X).symm
    (copower.indexHom.id X (Δ[1] : SSet.{w}))
    (min.homotopy X)

/-- The zero-endpoint concrete contraction gives the corresponding zigzag homotopy relation. -/
@[stacks 019O "zero-endpoint cylinder homotopy relation"]
theorem endpointZero.comp_homotopic_id :
    Homotopic
      (copower.projection X (Δ[1] : SSet.{w}) ≫ endpointZero X)
      (𝟙 (SimplicialObject.copower (Δ[1] : SSet.{w}) X)) := sorry

/-- Lemma 14.26.8 (2): the identity of the simplicial cylinder is homotopic to projection
followed by the zero endpoint. -/
@[stacks 019O "simplicial cylinder contraction to the zero endpoint"]
theorem endpointZero.id_homotopic_projection :
    Homotopic (𝟙 (SimplicialObject.copower (Δ[1] : SSet.{w}) X))
      (copower.projection X (Δ[1] : SSet.{w}) ≫ endpointZero X) := sorry

/-- Lemma 14.26.8 (3): the identity of the simplicial cylinder is homotopic to projection
followed by the one endpoint. -/
@[stacks 019O "simplicial cylinder contraction to the one endpoint"]
theorem endpointOne.id_homotopic_projection :
    Homotopic (𝟙 (SimplicialObject.copower (Δ[1] : SSet.{w}) X))
      (copower.projection X (Δ[1] : SSet.{w}) ≫ endpointOne X) := sorry

/-- The identity of the simplicial cylinder is homotopic to projection followed by either
endpoint. -/
@[stacks 019O "simplicial cylinder contraction to either endpoint"]
theorem endpoint.id_homotopic_projection (i : Fin 2) :
    Homotopic (𝟙 (SimplicialObject.copower (Δ[1] : SSet.{w}) X))
      (copower.projection X (Δ[1] : SSet.{w}) ≫ endpoint X i) := sorry

/-- The cylinder projection and a selected endpoint form a structured simplicial homotopy
equivalence. -/
@[stacks 019O "simplicial cylinder projection homotopy equivalence"]
def projection.homotopyEquiv (i : Fin 2) :
    HomotopyEquiv (SimplicialObject.copower (Δ[1] : SSet.{w}) X) X where
  hom := copower.projection X (Δ[1] : SSet.{w})
  inv := endpoint X i
  hom_inv_id := (endpoint.id_homotopic_projection X i).symm
  inv_hom_id := Homotopic.of_eq (endpoint.comp_projection X i)

/-- The forward map of the cylinder projection homotopy equivalence is the canonical
projection. -/
@[simp, stacks 019O "forward map of the cylinder projection homotopy equivalence"]
theorem projection.homotopyEquiv.hom (i : Fin 2) :
    (projection.homotopyEquiv X i).hom =
      copower.projection X (Δ[1] : SSet.{w}) := sorry

/-- The inverse map of the cylinder projection homotopy equivalence is the selected endpoint. -/
@[simp, stacks 019O "inverse map of the cylinder projection homotopy equivalence"]
theorem projection.homotopyEquiv.inv (i : Fin 2) :
    (projection.homotopyEquiv X i).inv = endpoint X i := sorry

/-- The simplicial-cylinder projection is a homotopy equivalence. -/
@[stacks 019O "simplicial cylinder projection is a homotopy equivalence"]
theorem projection.isHomotopyEquivalence :
    IsHomotopyEquivalence (copower.projection X (Δ[1] : SSet.{w})) := sorry

end CategoryTheory.SimplicialObject.copower.deltaOne
