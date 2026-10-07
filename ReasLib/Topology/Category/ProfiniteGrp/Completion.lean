module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- Open normal subgroups of finite index, used to index the topology-sensitive profinite
completion of a topological group. -/
abbrev OpenFiniteIndexNormalSubgroup (G : Type u) [Group G] [TopologicalSpace G] :=
  ObjectProperty.FullSubcategory
    (fun H : OpenNormalSubgroup G ↦ H.toSubgroup.FiniteIndex)

namespace OpenFiniteIndexNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- An object of `OpenFiniteIndexNormalSubgroup G` supplies the finite-index instance for its
underlying subgroup. -/
instance instFiniteIndex (H : OpenFiniteIndexNormalSubgroup G) : H.obj.toSubgroup.FiniteIndex :=
  H.property

/-- The underlying open normal subgroup. -/
abbrev toOpenNormalSubgroup (H : OpenFiniteIndexNormalSubgroup G) : OpenNormalSubgroup G := H.obj

/-- The finite quotient attached to an open finite-index normal subgroup. -/
def quotient (H : OpenFiniteIndexNormalSubgroup G) : FiniteGrp.{u} :=
  FiniteGrp.of (G ⧸ H.obj.toSubgroup)

/-- The quotient map induced by an inclusion of open finite-index normal subgroups. -/
def quotientMap {H K : OpenFiniteIndexNormalSubgroup G} (f : H ⟶ K) :
    quotient H ⟶ quotient K :=
  FiniteGrp.ofHom (QuotientGroup.map _ _ (MonoidHom.id G) f.hom.le)

/-- Quotient maps preserve identity morphisms. -/
theorem quotientMap_id (H : OpenFiniteIndexNormalSubgroup G) :
    quotientMap (𝟙 H) = 𝟙 (quotient H) := sorry

/-- Quotient maps preserve composition. -/
theorem quotientMap_comp {H K L : OpenFiniteIndexNormalSubgroup G}
    (f : H ⟶ K) (g : K ⟶ L) :
    quotientMap (f ≫ g) = quotientMap f ≫ quotientMap g := sorry

end OpenFiniteIndexNormalSubgroup

namespace TopologicalProfiniteCompletion

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The finite quotient diagram indexed by open finite-index normal subgroups. -/
def finiteDiagram : OpenFiniteIndexNormalSubgroup G ⥤ FiniteGrp.{u} where
  obj := OpenFiniteIndexNormalSubgroup.quotient
  map := OpenFiniteIndexNormalSubgroup.quotientMap
  map_id := OpenFiniteIndexNormalSubgroup.quotientMap_id
  map_comp := OpenFiniteIndexNormalSubgroup.quotientMap_comp

/-- The open finite-index quotient diagram viewed in profinite groups. -/
def diagram : OpenFiniteIndexNormalSubgroup G ⥤ ProfiniteGrp.{u} :=
  finiteDiagram G ⋙ CategoryTheory.forget₂ FiniteGrp ProfiniteGrp

/-- The topology-sensitive profinite completion, formed from open finite-index normal
subgroups. -/
noncomputable abbrev completion : ProfiniteGrp.{u} := ProfiniteGrp.limit (diagram G)

/-- The compatible family of quotient classes defined by an element of `G`. -/
def etaFn (x : G) : completion G :=
  (⟨fun _ ↦ QuotientGroup.mk x, fun _ _ _ ↦ rfl⟩ :
    ProfiniteGrp.limitConePtAux (diagram G))

/-- The pointwise map to the topology-sensitive completion is a monoid homomorphism. -/
def etaMonoidHom : G →* completion G where
  toFun := etaFn G
  map_one' := sorry
  map_mul' _ _ := sorry

/-- The canonical map to the topology-sensitive completion is continuous. -/
theorem eta_continuous [IsTopologicalGroup G] : Continuous (etaMonoidHom G) := sorry

/-- The canonical continuous homomorphism to the topology-sensitive profinite completion. -/
def eta [IsTopologicalGroup G] : G →ₜ* completion G :=
  { etaMonoidHom G with continuous_toFun := eta_continuous G }

/-- The canonical map evaluates to the family of quotient classes of its input. -/
theorem eta_apply [IsTopologicalGroup G] (x : G) : eta G x = etaFn G x := sorry

/-- The canonical map to the topology-sensitive profinite completion has dense range. -/
theorem denseRange_eta [IsTopologicalGroup G] : DenseRange (eta G) := sorry

end TopologicalProfiniteCompletion

end CategoryTheory
